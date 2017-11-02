open Printf

let () = Printexc.record_backtrace true 

(* ******************* *)
(* Constantes globales *)
(* ******************* *)

let p = int_of_string Sys.argv.(1) (* Taille de l'échiquier *) 
let execute_classique = (p <= 10) (* Au dessus, c'est long... *)
let cste = 19 (* pour la fonction de hachage *)
let h = 10_000_000_019 (* Un grand nombre premier *)

(* Les tailles des différentes tables de hachage.
 * Ces valeurs donnent des facteurs de charge raisonnables pour la méthode par
 * fusions successives. Quand on travaille colonne par colonne (et qu'on crée
 * plus d'arbres, il vaudrait mieux les prendre un peu plus grandes.
*)
let taille_arbre, taille_inter, taille_card =
  p + 9, p + 10, p + 6

let n = p * (p - 1) * 2 (* possibilités de placer un domino *)

(* ******************* *)
(* Références globales *)
(* ******************* *)

let case = ref 0 (* case de l'échiquier *)

type ac2 = A of int [@@ unboxed]

type unique = U of int [@@ unboxed]

type domino = D of int [@@ unboxed]                       

let id_size = 26
                       
let root (A x) =
  if x = 0 || x = 1 then D (max_int)
  else D (x lsr (2 * id_size))

let left (A x) = U ((x lsr id_size) land (1 lsl id_size - 1))

let right (A x) = U (x land (1 lsl id_size - 1))

let top = A 1
let id_top = U 1
            
let bottom = A 0
let id_bottom = U 0

let comb (D i) (U a) (U b) = A (i lsl (2 * id_size) + a lsl id_size + b)

let int_of_ac2 (A x) = x                                                     

let arbres_max = min (1 lsl id_size) (1 lsl (2 * p))
                                                     
let egal : ac2 -> ac2 -> bool = (=)

let arbres = Array.make arbres_max bottom
let () = arbres.(1) <- top
                        
let get_arbre (U i) = arbres.(i)

let set_arbre i a = arbres.(i) <- a

let sans x = get_arbre (left x)
let avec x = get_arbre (right x)                       

let limite_charge = 3

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

let hache x = abs (x + (x * x) mod h) 
             
let trouve {t; capacite} x =
  assert (x <> vide);
  let hash = hache x in
  let taille = 1 lsl capacite in
  let i0 = 2 * (hash mod (taille / 2)) in
  let i = ref i0 in
  let delta = ref 1 in
  while t.(!i) <> x && t.(!i) <> vide do
    i := (!i + !delta * (!delta + 1)) mod taille;
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
  if charge * limite_charge > taille then (assert false); (*redimensionne table;*)
  let hash = hache cle in
  let i0 = 2 * (hash mod (taille / 2)) in
  let i = ref (i0) in
  let delta = ref 1 in
  assert (0 <= !i && taille = Array.length t);
  while t.(!i) <> vide do
    i := (!i + !delta * (!delta + 1)) mod taille;
    if !i = i0 then printf "i0 : %i, delta : %i, taille : %i, charge : %i"
                           i0 !delta taille table.charge;
    assert (!i <> i0)
  done;
  t.(!i) <- cle;
  t.(!i + 1) <- valeur;
  table.charge <- table.charge + 1

let table_arbres =
  {capacite = taille_arbre;
   charge = 0;
   t = Array.make (1 lsl taille_arbre) vide}

let () =
  ajoute table_arbres (int_of_ac2 bottom) 0;
  ajoute table_arbres (int_of_ac2 top) 1

let trouve_arbre (A x) = trouve table_arbres x
let ajoute_arbre (A x) (U i) = ajoute table_arbres x i                                
                                   
let legal i a1 a2 =
  a2 <> bottom &&  i < min (root a1) (root a2)
                                   
let make_cons () =
  let id = ref 2 in
  let cons (D i) id1 id2 =
    (* assert (table_arbres.charge = !id); *)
    let arbre = comb (D i) id1 id2 in
    if not (legal (D i) (get_arbre id1) (get_arbre id2)) then
      (printf "D %i, arbre %i, arbre %i\n" i
              (int_of_ac2 @@ get_arbre id1)
              (int_of_ac2 @@ get_arbre id2);
       assert false);
                  
    match trouve_arbre arbre with
    | Some x -> U x
    | None ->  set_arbre !id arbre;
               ajoute_arbre arbre (U !id);
               incr id;
               U (!id - 1) in
  let get_next_id () = !id in
  cons, get_next_id

let cons, get_next_id = make_cons ()

(* Pour parcourir l'échiquier en diagonale *)
let case_suivante () =
  if !case mod p = 0 && !case/p < p-1 then case := !case/p + 1
  else if !case/p = p-1 then case := p * (!case mod p + 2) - 1
  else case := !case + (p-1)


(* Construction de la matrice de booléens *)
let m =
  let t = Array.make_matrix n (p * p) false
  and ligne = ref 0 in
  for k = 0 to p*p-1 do
    if !case mod p <> p-1 then
      begin
      t.(!ligne).( !case ) <- true;
      t.(!ligne).( !case + 1 ) <- true;
      incr ligne;
      end;
    if !case/p <> p-1 then
      begin
      t.(!ligne).( !case ) <- true;
      t.(!ligne).( !case + p ) <- true;
      incr ligne;
      end;
    case_suivante()
  done;
  t

(* _________________ *)
(* Fonction Cardinal *)
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

(* ______________ *)
(* Fonction Inter *)
let table_inter =
  {t = Array.make (1 lsl taille_inter) vide;
   capacite = taille_inter;
   charge = 0}

let ajoute_inter (U id1) (U id2) (U id_inter) =
  let cle = id1 + (id2 lsl id_size) in
  ajoute table_inter cle id_inter

let trouve_inter (U id1) (U id2) =
  let cle = id1 + (id2 lsl id_size) in
  trouve table_inter cle
    
let rec inter ida idb =
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


(* ________________ *)
(* Fonction Colonne *)
(* On commence par construire l'arbre des singletons correspondants 
aux dominos recouvrant la case, puis on ajoute les autres valeurs 
une par une en partant de la dernière *)

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
(*
  match get_arbre a with (* l'ajout d'un élément *)
    | Zero -> Zero
    | Un -> cons k Un Un
    | Comb(_,i,_,_) when k<i -> cons k a a
    | Comb(_,i,a1,a2) when k>i -> cons i (ajout k a1) (ajout k a2)
    | _ -> failwith "Erreur Ajout"
 *)
                               
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
  case := 0;
  let arbre = ref (colonne 0) in
  for k = 1 to p*p-1 do
    case_suivante();
    arbre := inter !arbre (colonne !case)
  done;
  !arbre


let pavage2 () =
  let rec aux i =
    if i = p * p then []
    else begin
      let c = colonne !case in
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
  case := 0;
  fusionne @@ aux 0


(* ________________________ *)
(* Résultat et statistiques *)

let chrono f x =
  let t0 = Sys.time () in
  let y = f x in
  (y, Sys.time() -. t0)

    
let stats_table table nom_table =
  let longueurs = Array.map List.length table in
  let somme, maxi =
    Array.fold_left (fun (s, m) u -> (s + u, max m u)) (0, 0) longueurs in
  let seaux = Array.make (maxi + 1) 0 in
  let taille = Array.length table in
  for k = 0 to taille - 1 do
    let l = List.length (table.(k)) in
    seaux.(l) <- seaux.(l)+1
  done;
  printf "\nPour la table %s :\n" nom_table;
  printf " Taille : %i\n" taille;
  printf " Nombre d'éléments : %i\n" somme;
  printf " Facteur de charge : %.2f\n" @@ (float somme /. float taille);
  printf " Maximum des tailles des seaux : %i\n" maxi
  (* printf " Nombre de seaux de longueur :\n";
     Array.iteri (printf " %2i : %i\n") seaux *)


let affiche fonction_pavage nom_fonction =
  let sep = String.make 80 '=' in
  printf "%s\n%s\n%s\n" sep nom_fonction sep;
  let id_arbre, t_constr = chrono fonction_pavage () in
  let card, t_card = chrono cardinal (get_arbre id_arbre) in
  printf "Nombre de pavages possibles : %i\n" card;
  printf "Temps de construction : %.2fs\n" t_constr;
  printf "Temps de calcul du cardinal : %.2fs\n" t_card;
  printf "Nombre d'arbres distincts construits : %i\n" (get_next_id ())
  (*stats_table tableArbre "Arbre";
  stats_table tableInter "Inter";
  stats_table tableCardinal "Card"*)


let main () =
  (*Gc.set {(Gc.get ()) with Gc.space_overhead = 400};*)
  (*if execute_classique then begin
    affiche pavage "Colonne par colonne";
    id_unique := 2;
    let reinit t =
      let n = Array.length t in
      Array.blit (Array.make n []) 0 t 0 n in
    reinit tableArbre; reinit tableInter; reinit tableCardinal;
    Gc.full_major ()
    end;*)
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
