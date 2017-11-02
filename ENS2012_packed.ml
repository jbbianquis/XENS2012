open Printf

let () = assert (Printexc.record_backtrace true; true)

(* ******************* *)
(* Constantes globales *)
(* ******************* *)

let p = int_of_string Sys.argv.(1) (* Taille de l'échiquier *) 
let n = p * (p - 1) * 2 (* possibilités de placer un domino *)
let execute_classique = (p <= 10) (* Au dessus, c'est long... *)


(* Les tailles des différentes tables de hachage.
 * Ces valeurs donnent des facteurs de charge raisonnables pour la méthode par
 * fusions successives. Quand on travaille colonne par colonne (et qu'on crée
 * plus d'arbres), il vaudrait mieux les prendre un peu plus grandes.
 * Noter qu'avec ces valeurs, il n'y a jamais de redimensionnement des tables !
 * En prenant des valeurs plus petites, ce sera donc un peu plus lent.
*)
let taille_arbre, taille_inter, taille_card =
  p + 9, p + 10, p + 6
(* On redimensionne quand facteur de charge >= 2 / limite_charge.
 * Valeur optimale : 3, 4 est aussi raisonnable. 
 *)
let limite_charge = 3
let () = assert (limite_charge > 2)                    

let h = 10_000_000_019 (* Un grand nombre premier *)


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

                  
(* Étiquette de la racine. 
 *  On renvoie max_int si l'arbre vaut bottom ou top pour assurer 
 * l'invariant root a < min (root (left a)) (root (right a)).
 *)                         
let root (A x) : domino =
  if (A x) = bottom || (A x) = top then D (max_int)
  else D (x lsr (2 * id_size))

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

(* Taille du tableau contenant les arbres. 
 * Plus de 2^id_size ne sert évidemment à rien, 
 * et le 2^(2*p + 3) (valeur expérimentale...) permet d'éviter de consommer 
 * trop de mémoire inutile pour les petites instances. 
 * Au maximum, on utilise (pour ce tableau) 2^29 octets ~ 500 Mo. 
 *)
let arbres_max = min (1 lsl id_size) (1 lsl (2 * p + 3))
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

(* Peu importe, en fait. *)
let hache x = abs (x + (x * x) mod h) 


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
  let delta = ref 1 in
  while t.(!i) <> cle && t.(!i) <> vide do
    i := (!i + !delta * (!delta + 1)) land mask;
  done;
  if t.(!i) = vide then None
  else Some t.(!i + 1)

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
  if charge * limite_charge >= taille then redimensionne table;
  let mask = taille - 1 in
  let hash = hache cle in
  let i0 = 2 * (hash land (mask lsr 1)) in
  let i = ref (i0) in
  let delta = ref 1 in
  assert (0 <= !i && !i < taille && taille = Array.length t);
  while t.(!i) <> vide do
    i := (!i + !delta * (!delta + 1)) land mask;
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

(* Pour parcourir l'échiquier en diagonale *)
let enumerateur_cases () =
  let case = ref 0 in 
  let case_suivante () =
    if !case mod p = 0 && !case/p < p-1 then case := !case/p + 1
    else if !case/p = p-1 then case := p * (!case mod p + 2) - 1
    else case := !case + (p-1) in
  let num_case () = !case in
  case_suivante, num_case


(* Construction de la matrice de booléens *)
let m =
  let t = Array.make_matrix n (p * p) false
  and ligne = ref 0 in
  let case_suivante, case = enumerateur_cases () in
  for k = 0 to p*p-1 do
    if case () mod p <> p-1 then
      begin
      t.(!ligne).(case () ) <- true;
      t.(!ligne).(case () + 1) <- true;
      incr ligne;
      end;
    if case () / p <> p-1 then
      begin
      t.(!ligne).(case ()) <- true;
      t.(!ligne).(case () + p ) <- true;
      incr ligne;
      end;
    case_suivante ()
  done;
  t


let domino j = (* la liste des dominos couvrant la case *)
    let rec aux acc = function
        | -1 -> acc
        | k -> if m.(k).(j) then aux (D k :: acc) (k - 1) else aux acc (k - 1)
    in aux [] (n-1)


let rec singletons = function (* l'arbre des singletons *)
    | [] -> id_bottom
    | a::q -> cons a (singletons q) id_top

let rec ajout k ida =
  let a = get_arbre ida in
  if a = bottom then id_bottom
  else if a = top then cons k id_top id_top
  else if k < root a then cons k ida ida
  else if k > root a then
    try cons (root a) (ajout k (left a)) (ajout k (right a))
    with e -> printf "a : %i, k : %i"
                     (int_of_ac2 a) ((fun (D x) -> x) k);
              raise e
  else failwith "Erreur ajout"
                               
let colonne j = (* la construction de l'arbre complet *)
    let d = domino j in
    let s = singletons d in
    let rec aux acc = function
        | -1 -> acc
        | k when List.mem (D k) d -> aux acc (k-1)
        | k ->  aux (ajout (D k) acc) (k-1)
    in aux s (n-1)

(* _______________ *)
(* Fonction Pavage *)

let pavage () =
  let case_suivante, case = enumerateur_cases () in
  let arbre = ref (colonne 0) in
  for k = 1 to p*p-1 do
    case_suivante ();
    arbre := inter !arbre (colonne (case ()))
  done;
  !arbre


let pavage2 () =
  let case_suivante, case = enumerateur_cases () in
  let rec aux i =
    if i = p * p then []
    else begin
      let c = colonne (case ()) in
      case_suivante ();
      c :: aux (i + 1)
    end in
  let rec une_passe = function
    | x :: y :: xs -> inter x y :: une_passe xs
    | u -> u in
  let rec fusionne = function
    | [] -> failwith "fusionne"
    | [x] -> x
    | u -> fusionne @@ une_passe u in
  fusionne @@ aux 0


(* ________________________ *)
(* Résultat et statistiques *)

let chrono f x =
  let t0 = Sys.time () in
  let y = f x in
  (y, Sys.time() -. t0)

let affiche fonction_pavage nom_fonction =
  let sep = String.make 80 '=' in
  printf "%s\n%s\n%s\n" sep nom_fonction sep;
  let id_arbre, t_constr = chrono fonction_pavage () in
  let card, t_card = chrono cardinal (get_arbre id_arbre) in
  let card_long, t_card_long = chrono cardinal_long (get_arbre id_arbre) in
  printf "Nombre de pavages possibles : %i\n" card;
  printf "Et en précision arbitraire : %s\n" (Z.to_string card_long);
  printf "Temps de construction : %.2fs\n" t_constr;
  printf "Temps de calcul du cardinal : %.2fs\n" t_card;
  printf "Temps de calcul du cardinal en précision arbitraire : %.2fs\n" t_card_long;
  printf "Nombre d'arbres distincts construits : %i\n" (get_next_id ())
  (*stats_table tableArbre "Arbre";
  stats_table tableInter "Inter";
  stats_table tableCardinal "Card"*)


let main () =
  try 
    affiche pavage2 "\"Diviser pour régner\"";
    printf "Nombre d'arbres construits : %i\n" (get_next_id ());
    printf "Taille du tableau arbres : %i\n" (arbres_max);
    printf "Table arbres : taille %i, utilisée %i\n"
           (1 lsl (table_arbres.capacite - 1))
           table_arbres.charge;
    printf "Table inter : taille %i, utilisée %i\n"
           (1 lsl (table_inter.capacite - 1))
           table_inter.charge;
  with
  | e -> 
         printf "Nombre d'arbres construits : %i\n" (get_next_id ());
         printf "Taille du tableau arbres : %i\n" (arbres_max);
         printf "Table arbres : taille %i, utilisée %i\n"
                (1 lsl (table_arbres.capacite - 1))
                table_arbres.charge;
         printf "Table inter : taille %i, utilisée %i\n"
                (1 lsl (table_inter.capacite - 1))
                table_inter.charge;
         raise e

  
let () = main ()
