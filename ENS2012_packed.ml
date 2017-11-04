open Printf

let () = assert (Printexc.record_backtrace true; true)

(* ******************* *)
(* Constantes globales *)
(* ******************* *)

(* Premier argument en ligne de commande : taille de l'échiquier *)
let p = int_of_string Sys.argv.(1) (* Taille de l'échiquier *)

(* Choix de l'ordre d'énumération des cases. 
 * Voir plus bas pour les choix possibles. *)
let enum = "diagonales_sans_saut"
  
let n = p * (p - 1) * 2 (* possibilités de placer un domino *)
let t0 = Sys.time ()

(* Les tailles des différentes tables de hachage.
 * Ces valeurs donnent des facteurs de charge raisonnables pour la méthode par
 * fusions successives. Quand on travaille colonne par colonne (et qu'on crée
 * plus d'arbres), il vaudrait mieux les prendre un peu plus grandes.
 * Noter qu'avec ces valeurs, il n'y a jamais de redimensionnement des tables !
 * En prenant des valeurs plus petites, ce sera donc un peu plus lent.
*)
let taille_arbre, taille_inter, taille_card =
  p + 8, p + 10, p + 5
(* On redimensionne quand facteur de charge * 128 >= limite_charge.
 * Le coût d'une recherche est généralement dominé par le coût du
 * cache miss sur le premier accès (~85% du coût total), il est 
 * donc contre-productif de chercher à avoir un facteur de 
 * charge trop petit.
 *)
let limite_charge = 96

let h = 100_000_000_003 (* Un grand nombre premier *)


(******************************************************************************)
(*    Définitions des types et des opérations élémentaires sur les arbres     *)
(******************************************************************************)
               
(* Laisse 63 - 2*26 = 11 bits pour le numéro du domino.
 * OK si n <= 2047, i.e. p <= 32.
 * On ne peut construire que 2^id_size ~ 67 millions d'arbres
 * distincts, donc de toute façon p > 32 est irréaliste.
 *)                  
let id_size = 26
               
(* Un arbre combinatoire est codé sur 63 bits de la manière suivante :
 * - 11 bits de poids fort : étiquette de la racine (type domino)
 * - 26 bits suivants : id_unique du fils gauche
 * - 26 derniers bits : id_unique du fils droit
 * - le dernier bit de l'entier est le tag de Caml (donc il vaut 1).
 *
 * L'id_unique d'un arbre est simplement son indice dans le tableau
 * qui contient tous les arbres alloués. Essentiellement, on utilise
 * un allocateur manuel linéaire puisqu'on sait qu'on ne voudra jamais 
 * désallouer un arbre avant la fin du programme.
 * 
 * Les entiers 0 et 1 codent respectivement bottom et top (dont les 
 * identifiants uniques valent aussi 0 et 1).
 * Le code suppose que min_int n'est pas la représentation d'un arbre,
 * mais de toute façon c'est impossible (l'id_unique 2^26 - 1 étant 
 * le plus grand possible, il ne peut pas apparaître comme un fils
 * d'un autre arbre.
 *
 * Les types sont différenciés pour avoir une chance d'écrire du 
 * code correct, l'indication [@@ unboxed] permet d'éliminer
 * toutes ces boîtes à la compilation. Autrement dit, le code compilé
 * est exactement le même que si l'on avait mis "type ac = int" et 
 * ainsi de suite.
 * Pour information, c'est environ 2.5x plus lent si l'on enlève les
 * [@@ unboxed] !
 *
 * L'égalité entre deux arbres est tout simplement l'égalité sur les entiers.
 *)
type ac = A of int [@@ unboxed]
type unique = U of int [@@ unboxed]
type domino = D of int [@@ unboxed]

let bottom = A 0
let id_bottom = U 0                     
let top = A 1
let id_top = U 1

(* Taille du tableau contenant les arbres. 
 * Plus de 2^id_size ne sert évidemment à rien (cf plus bas), 
 * et le 2^(p + 7) (valeur expérimentale...) permet d'éviter de consommer 
 * trop de mémoire inutile pour les petites instances. 
 * Au maximum, on utilise (pour ce tableau) 2^29 octets = 512 Mo. 
 *)
let arbres_max = min (1 lsl id_size) (1 lsl (p + if enum = "diagonales_sans_saut" then 7 else 10))

               
                  
(* Étiquette de la racine. 
 * Il est illégal d'appeler cette fonction sur bottom ou top.
 *)                         
let root (A x) : domino =
  assert ((A x) <> bottom && (A x) <> top);
  D (x lsr (2 * id_size))

(* Identifiants uniques des fils gauche et droit. *)
let left (A x) : unique =
  assert (A x <> top && A x <> bottom);
  U ((x lsr id_size) land (1 lsl id_size - 1))
let right (A x) : unique =
  assert (A x <> top && A x <> bottom);
  U (x land (1 lsl id_size - 1))

(* Construit un arbre à partir de sa racine et des id de ses fils. *)            
let comb (D i) (U a) (U b) : ac = A (i lsl (2 * id_size) + a lsl id_size + b)

(* Déballe un arbre. On en a besoin deux ou trois fois. *)                                    
let int_of_ac2 (A x) = x                                                     

let arbres = Array.make arbres_max bottom
let () = arbres.(1) <- top

(* Renvoie l'arbre correspondant à un id. La fonction pour rajouter un arbre
 * n'est pas exposée.
 *)
let get_arbre (U i) : ac = arbres.(i)

(* sous-arbre gauche, sous-arbre droit *)                                 
let sans (x : ac) : ac = get_arbre (left x)
let avec (x : ac) : ac = get_arbre (right x)                       

(******************************************************************************)
(*               Fonctions de base sur les tables de hachage                  *)
(******************************************************************************)

(* On utilise des tables de hachage avec quadratic probing. La séquence 
 * de recherche est conplète à condition que la taille soit une puissance 
 * de 2 (ce qui sera toujours le cas).
 * Ces tables supposent que clés et valeurs tiennent chacune sur un entier ;
 * tout est stocké dans la table, il n'y a pas de pointeur.
 * Comme on ne stocke pas le hash dans la table, il faut tout re-hacher si 
 * l'on redimensionne : ce n'est pas un problème ici, la fonction de hachage
 * a un coùt négligeable (et de toute façon on peut éviter de re-dimensionner).
 *
 * Pour simplifier, on fixe le type des clés et des valeurs à int (on définira 
 * à chaque fois une fonction bas niveau faisant l'interface). S'il on prend
 * un type polymorphe, il faut mettre la fonction de hachage dans le 
 * record, ainsi que la fonction d'égalité à utiliser (sinon on passe sur la 
 * comparaison polymorphe, ce qui sera sans doute catastrophique).
 * 
 *)
                      
(* Array.size t = 2^capacite
 * t.(2i) : clé, t.(2i + 1) : valeur associée
 * clé min_int interdite
 * charge : nombre de couples (clé, valeur)
 * facteur de charge = 2^capacite / (2 * charge)
 *)                      
type hash_table = {mutable capacite : int;
                   mutable charge : int;
                   mutable t : int array}
let vide = min_int

(* Marche plutôt bien, pas trop coûteux à calculer. *)
let hache x = abs ((x + x lsl (1 + id_size)) mod h) 


(* Le compilateur n'est pas capable de se rendre compte que 
 * taille est une puissance de 2 et fait des idiv à chaque fois.
 * Donc les shift sont codés à la main.
 *)
let trouve ({t; capacite} : hash_table) (cle : int) : int option =
  assert (cle <> vide);
  let hash = hache cle in
  let taille = 1 lsl capacite in
  (* x land mask = x mod taille *)
  let mask = taille - 1 in 
  let i0 = 2 * (hash land (mask lsr 1)) in
  let i = ref i0 in
  (* Je n'ai pas encore compris pourquoi, mais traiter séparément 
   * le premier cas a un impact mesuralble sur les perfs. 
   * Au départ, j'avais juste mis ça pour avoir les cache miss 
   * séparément sur le premier accès et les autres, mais résultat
   * je le laisse. *)
  if t.(!i) = vide then None
  else if t.(!i) = cle then Some t.(!i + 1)
  else begin
      let delta = ref 2 in
      while t.(!i) <> vide && t.(!i) <> cle do
        i := (!i + !delta) land mask;
        delta := !delta + 2;
        assert (!i <> i0)
      done;
      if t.(!i) = vide then None
      else Some t.(!i + 1)
    end
    

let rec redimensionne ({t; charge; capacite} as table) =
  let taille = 1 lsl capacite in
  let nv_t = Array.make (2 * taille) vide in
  (table.t <- nv_t; table.capacite <- capacite + 1; table.charge <- 0);
  for i = 0 to (taille - 1) / 2 do
    if t.(2 * i) <> vide then ajoute table t.(2 * i) t.(2 * i + 1)
  done        
and ajoute ({capacite; charge; t} as table) cle valeur =
  assert (cle <> vide);
  let taille = 1 lsl capacite in
  if taille * limite_charge <= charge * 256 then redimensionne table;
  let mask = taille - 1 in
  let hash = hache cle in
  let i0 = 2 * (hash land (mask lsr 1)) in
  let i = ref (i0) in
  let delta = ref 2 in
  while t.(!i) <> vide do
    i := (!i + !delta) land mask;
    delta := !delta + 2;
    assert (!i <> i0)
  done;              
  t.(!i) <- cle;
  t.(!i + 1) <- valeur;
  table.charge <- table.charge + 1

(******************************************************************************)
(*     Construction des arbres, table de hachage arbre -> id                  *)
(******************************************************************************)

(* Tout est privé sauf la fonction cons (bien sûr) et une fonction permettant 
 * de savoir combien d'arbres on a construit (qui ne sert que pour les stats
 * à la fin).
 *)

let table_arbres =
  {capacite = taille_arbre;
   charge = 0;
   t = Array.make (1 lsl taille_arbre) vide} 

let () = 
  ajoute table_arbres (int_of_ac2 bottom) 0;
  ajoute table_arbres (int_of_ac2 top) 1

let trouve_arbre ((A x) : ac) : int option = trouve table_arbres x 
let ajoute_arbre (A x) (U i) = ajoute table_arbres x i
                                   
let make_cons () =
  (* !id = nombre d'arbres déjà créés = id du prochain arbre créé *)
  let id = ref 2 in
  (* Vérifie que l'arbre demandé est "légal" (fils droit non réduit à 
   * bottom, étiquettes strictement croissantes à partir de la racine. *)
  let legal (i : domino) (a1 : ac) (a2 : ac) =
    a2 <> bottom &&  i < min (root a1) (root a2) in
  (* crée un nouvel arbre et renvoie son id *)
  let cree_arbre (a : ac) : unique =
    arbres.(!id) <- a;
    incr id;
    U (!id - 1) in
  let cons (D i) id1 id2 =
    (* assert (table_arbres.charge = !id); *)
    let arbre = comb (D i) id1 id2 in
    (* if not (legal (D i) (get_arbre id1) (get_arbre id2)) then
      (printf "D %i, arbre %i, arbre %i\n" i
              (int_of_ac2 @@ get_arbre id1)
              (int_of_ac2 @@ get_arbre id2);
       assert false); *)
    assert (legal (D i) (get_arbre id1) (get_arbre id2));
    match trouve_arbre arbre with
    | Some x -> U x
    | None ->  let id_cree = cree_arbre arbre in
               ajoute_arbre arbre id_cree;
               id_cree  in
  let get_next_id () = !id in
  cons, get_next_id

let cons, get_next_id = make_cons ()

(******************************************************************************)
(*    Calcul de l'intersection, table de hachage id x id -> id                *)
(******************************************************************************)

(* Les clés sont des couples (id, id), codés simplement sur un entier
 * (un id sur les 26 bits de poids faibles, l'autre sur les 26 bits suivants).
 *)
let table_inter =
  {t = Array.make (1 lsl taille_inter) vide;
   capacite = taille_inter;
   charge = 0}

let ajoute_inter (U id1) (U id2) (U id_inter) : unit =
  let cle = id1 + (id2 lsl id_size) in
  ajoute table_inter cle id_inter

let trouve_inter (U id1) (U id2) : int option =
  let cle = id1 + (id2 lsl id_size) in
  trouve table_inter cle
    
let rec inter (ida : unique) (idb : unique) : unique =
  if ida = idb then ida
  else if ida > idb then inter idb ida
  else if ida = id_bottom then id_bottom
  else if idb = id_top then id_top
  else
    match trouve_inter ida idb with
    | Some c -> U c
    | None ->
       let a = get_arbre ida and b = get_arbre idb in
       let idc =
         if a = top then inter ida (left b)
         else if root a < root b then inter (left a) idb
         else if root a > root b then inter ida (left b)
         else 
           let droite = inter (right a) (right b)
           and gauche = inter (left a) (left b) in
           if droite = id_bottom then gauche
           else cons (root a) gauche droite in
       ajoute_inter ida idb idc;
       idc

(******************************************************************************)
(*    Calcul du cardinal, table de hachage ac -> int                          *)
(******************************************************************************)

(* Les cardinaux ne rentrent rapidement plus dans un entier 63 bits. Les 
 * tables de hachage définies sont limitées à des valeurs entières (ou pouvant
 * être codées par un int, mais donc pas des pointeurs).
 * Vu que la table des cardinaux est assez petite, ce n'est pas un problème 
 * d'utiliser quelque chose d'un peu plus général si l'on veut faire les 
 * calculs en précision arbitraire. 
 *)
         
let table_card =
  {t = Array.make (1 lsl taille_card) vide;
   capacite = taille_card;
   charge = 0}

let ajoute_card (A x) n = ajoute table_card x n
let trouve_card (A x) = trouve table_card x

let () =
  ajoute_card bottom 0;
  ajoute_card top 1
                               
    
let rec cardinal a =
    match trouve_card a with
    | Some n -> n
    | None ->
       let n = cardinal (sans a) + cardinal (avec a) in
       ajoute_card a n;
       n

(* Version précision quelconque, nécessite zarith (ou de coder quelque chose
 * à la main, ce n'est pas très compliqué vu qu'on n'a besoin que de 
 * l'addition...).
 *)

let cardinal_long (a : ac)  =
  let module H = Hashtbl in
  let t = H.create 10_000 in
  H.add t bottom Z.zero;
  H.add t top Z.one;
  let rec card a =
    try H.find t a
    with
    | Not_found ->
       let n = Z.add (card (sans a)) (card (avec a)) in
       H.add t a n;
       n in
  card a
  

(* ________________ *)
(* Fonction Colonne *)
(* On commence par construire l'arbre des singletons correspondants 
aux dominos recouvrant la case, puis on ajoute les autres valeurs 
une par une en partant de la dernière *)
   
(* Pour parcourir l'échiquier en diagonale. Cf tab_of_enum *)
let enumerateur_maxime () =
  let case = ref 0 in 
  let case_suivante () =
    if !case mod p = 0 && !case/p < p-1 then case := !case/p + 1
    else if !case/p = p-1 then case := p * (!case mod p + 2) - 1
    else case := !case + (p-1) in
  let num_case () = !case in
  case_suivante, num_case

(* Pour parcourir en diagonale mais sans saut (on alterne diagonales 
 * ascendantes et descendantes. Cf tab_of_enum *)
let enumerateur_bis () =
  let case = ref 0 in
  let sens = ref 1 in
  let haut () = (!case < p) in
  let bas () = (!case + p >= p * p) in
  let gauche () = (!case mod p = 0) in
  let droite () = (!case mod p = p - 1) in
  let flip () = (sens := - !sens) in
  let case_suivante () =
    if gauche () && not (bas ()) && !sens = 1 then (case := !case + p; flip ())
    else if haut () && not (droite ()) && !sens = -1 then (incr case; flip ())
    else if bas () && not (droite ()) && !sens = 1 then (incr case; flip ())
    else if droite () && !sens = -1 then (case := !case + p; flip ())
    else case := !case + !sens * (p-1) in
  let num_case () = !case in
  case_suivante, num_case

(* Renvoie le tableau des numéros de case dans l'ordre défini par
 * l'énumération.
 * Pour p = 4, on a la numérotation :
 *  0  1  2  3
 *  4  5  6  7 
 *  8  9 10 11 
 * 12 13 14 15 
 * et les tableaux :
 * tab_of_enum enumerateur_maxime :
 *   [|0; 1; 4; 2; 5; 8; 3; 6; 9; 12; 7; 10; 13; 11; 14; 15|]
 * tab_of_enum enumerateur_bis :
 *   [|0; 4; 1; 2; 5; 8; 12; 9; 6; 3; 7; 10; 13; 14; 11; 15|]
 * Expérimentalement, enumerateur_bis est un peu meilleur et les 
 * deux sont bien meilleurs que l'enumération standard 
 * [|0; 1; 2; ... ; p*p - 1|].
 * Si l'on énumère les cases dans un ordre aléatoire, c'est complètement
 * catastrophique.
 *)
let tab_of_enum enum =
  let avance, case = enum () in
  Array.init (p * p) (fun i -> let x = case () in avance (); x)

let cases_diagonales_1 () = tab_of_enum enumerateur_maxime
let cases_diagonales_2 () = tab_of_enum enumerateur_bis

                                   
let tab_serpent () =
  let t = Array.init (p * p) (fun i -> i) in
  for ligne = 0 to p - 1 do
    if ligne mod 2 = 1 then
      for i = 0 to p - 1 do
        t.(ligne * p + i) <- ligne * p + p - i - 1
      done
  done;
  t
                 

let matrice cases =
  let t = Array.make_matrix n (p * p) false
  and ligne = ref 0 in
  for k = 0 to p*p-1 do
    if cases.(k) mod p <> p-1 then
      begin
      t.(!ligne).(cases.(k)) <- true;
      t.(!ligne).(cases.(k) + 1) <- true;
      incr ligne;
      end;
    if cases.(k) / p <> p-1 then
      begin
      t.(!ligne).(cases.(k)) <- true;
      t.(!ligne).(cases.(k) + p) <- true;
      incr ligne;
      end;
  done;
  t
   
let colonne m j =
  let rec remplie (D k) =
    if k = n then id_top
    else if m.(k).(j) then remplie (D (k + 1))
    else
      let a = remplie (D (k + 1)) in
      cons (D k) a a
  and a_remplir (D k) =
    if k = n then id_bottom
    else if m.(k).(j) then
      let avec_k = remplie (D (k + 1)) in
      let sans_k = a_remplir (D (k + 1)) in
      cons (D k) sans_k avec_k
    else
      let a = a_remplir (D (k + 1)) in
      if a = id_bottom then id_bottom
      else cons (D k) a a in
  a_remplir (D 0)     
                         
(* _______________ *)
(* Fonction Pavage *)


let pave ordre_cases =
  let rec une_passe = function
    | x :: y :: xs -> inter x y :: une_passe xs
    | u -> u in
  let rec fusionne = function
    | [] -> failwith "fusionne"
    | [x] -> x
    | u -> fusionne @@ une_passe u in
  ordre_cases
  |> Array.to_list
  |> List.map @@ colonne (matrice ordre_cases)
  |> fusionne

let pavage () =
  match enum with
  | "diagonales" -> pave (cases_diagonales_1 ())
  | "diagonales_sans_saut" -> pave (cases_diagonales_2 ())
  | "basique" -> pave (Array.init (p * p) (fun i -> i))
  | "basique_sans_saut" -> pave (tab_serpent ())
  | _ -> failwith "ordre d'enumeration inconnu"


(* ________________________ *)
(* Résultat et statistiques *)

let chrono f x =
  let t0 = Sys.time () in
  let y = f x in
  (y, Sys.time() -. t0)

let affiche_stats {t; charge; capacite} nom =
  let taille = 1 lsl capacite in
  printf "Stats de la table %s :\n" nom;
  printf " - occupation mémoire : %i Mo\n" (taille lsr 17);
  printf " - nombre de slots : %i\n" (1 lsl (capacite - 1));
  printf " - nombre de couples stockés : %i\n" charge;
  printf " - facteur de charge : %.2f\n" (float (2 * charge) /. float taille)

let main () =
    let sep = String.make 80 '=' in
    let t_alloc = Sys.time () -. t0 in
    let id_arbre, t_constr = chrono pavage () in
    let card, t_card = chrono cardinal (get_arbre id_arbre) in
    let card_long, t_card_long = chrono cardinal_long (get_arbre id_arbre) in
    print_endline sep;
    printf "Nombre de pavages possibles : %i\n" card;
    printf "Et en précision arbitraire : %s\n" (Z.to_string card_long);
    print_newline ();
    printf "Temps d'allocation initiale : %.2fs\n" t_alloc;
    printf "Temps de construction : %.2fs\n" t_constr;
    printf "Temps de calcul du cardinal : %.2fs\n" t_card;
    printf "Temps de calcul du cardinal en précision arbitraire : %.2fs\n"
           t_card_long;
    printf "Temps total d'exécution : %.2fs\n" (Sys.time () -. t0);
    print_endline sep;
    printf "Tableau arbres :\n";
    printf " - occupation mémoire : %i Mo\n" (arbres_max lsr 17);
    printf " - nombre de slots : %i\n" arbres_max;
    printf " - nombre d'arbres stockés (i.e. nombre d'arbres distincts construits) : %i\n"
           (get_next_id ());
    printf " - pourcentage d'utilisation : %.2f\n\n"
           (float (get_next_id ()) /. float arbres_max);
    affiche_stats table_arbres "arbres";
    print_newline ();
    affiche_stats table_inter "intersection";
    print_newline ();
    affiche_stats table_card "cardinal"
  
let () = main ()
