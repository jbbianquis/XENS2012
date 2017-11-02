open Printf

(* let () = Printexc.record_backtrace true *)

(* ******************* *)
(* Constantes globales *)
(* ******************* *)

let p = int_of_string Sys.argv.(1) (* Taille de l'échiquier *)
let execute_classique = (p <= 10) (* Au dessus, c'est long... *)
let cste = 19 (* pour la fonction de hachage *)
let h = 999_999_937 (* Un grand nombre premier *)

(* Les tailles des différentes tables de hachage.
 * Ces valeurs donnent des facteurs de charge raisonnables pour la méthode par
 * fusions successives. Quand on travaille colonne par colonne (et qu'on crée
 * plus d'arbres, il vaudrait mieux les prendre un peu plus grandes.
*)
let taille_arbre, taille_inter, taille_card = 1 lsl (p + 7), 1 lsl (p + 8), 1 lsl (p + 4)

let n = p * (p - 1) * 2 (* possibilités de placer un domino *)

(* ******************* *)
(* Références globales *)
(* ******************* *)
let case = ref 0 (* case de l'échiquier *)
let id_unique = ref 2 (* pour identifier les arbres *)


(* Les types utilisés *)
type unique = int
type ac =
  | Zero
  | Un
  | Comb of unique * int * ac * ac



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


let unique = function
  | Zero -> 0
  | Un -> 1
  | Comb(u,_,_,_) -> u

let egal a1 a2 = match (a1,a2) with
  | Zero,Zero | Un,Un -> true
  | Comb(_,i,l1,r1),Comb(_,j,l2,r2) -> (i=j) && (unique l1 = unique l2) && (unique r1 = unique r2)
  | _,_ -> false

let hache = function
    | Zero -> 0
    | Un -> 1
    | Comb(_,i,a1,a2) -> (cste*(cste*i + (unique a1)) + (unique a2)) mod h


(* _____________ *)
(* Fonction Cons *)

exception Absent

let tableArbre = Array.make taille_arbre []
let hache_arbre a = hache a land (taille_arbre - 1)

let ajouteArbre a =
    let hash = hache_arbre a in
    tableArbre.(hash) <- a::tableArbre.(hash)

let trouveArbre a =
    let seau = tableArbre.(hache_arbre a) in
    let rec valeur = function
        | c::_ when (egal c a) -> c
        | _::q -> valeur q
        | _ -> raise Absent
    in valeur seau

let cons i a1 a2 =
  try trouveArbre (Comb(0,i,a1,a2))
  with
    Absent ->
    let c = match (a1,a2) with
      | Comb(_,j,_,_),Comb(_,k,_,_) when i<j && i<k -> Comb(!id_unique,i,a1,a2)
      | _,Comb(_,k,_,_)  when i<k -> Comb(!id_unique,i,a1,a2)
      | Comb(_,j,_,_),Un when i<j -> Comb(!id_unique,i,a1,Un)
      | Zero,Un-> Comb(!id_unique,i,Zero,Un)
      | Un,Un  -> Comb(!id_unique,i,Un,Un)
      (* | Zero,Comb(_,k,_,_) when i<k -> Comb(!id_unique,i,Zero,a2) *)
      | _,_ -> print_int i; failwith "Erreur Construction"
    in incr id_unique; ajouteArbre c; c


(* _________________ *)
(* Fonction Cardinal *)
let tableCardinal = Array.make taille_card []
let hache_card a = hache a land (taille_card - 1)

let ajouteCard a v =
    let hash = hache_card a in
    tableCardinal.(hash) <- (unique a, v) :: tableCardinal.(hash)
let presentCard a =
    let seau = tableCardinal.(hache_card a) in
    let rec recherche = function
        | [] -> false
        | c::q -> fst c = unique a || recherche q
    in recherche seau
let trouveCard a =
    let seau = tableCardinal.(hache_card a) in
    let rec valeur = function
        | c::_ when fst c = unique a -> snd c
        | _::q -> valeur q
        | _ -> failwith "Absent"
    in valeur seau

let rec cardinal a =
    if presentCard a then trouveCard a
    else begin
        let c = match a with
            | Zero -> 0
            | Un -> 1
            | Comb(_,_,a1,a2) -> cardinal a1 + cardinal a2
        in ajouteCard a c; c
        end

(* ______________ *)
(* Fonction Inter *)
let tableInter = Array.make taille_inter []
let hache_inter a b = (hache a * hache b) land (taille_inter - 1)

let ajouteInter a b v =
    let hash = hache_inter a b in
    let seau = tableInter.(hash) in
    tableInter.(hash) <- (unique a, unique b, v) :: seau

let trouveInter a b =
    let hash = hache_inter a b in
    let seau = tableInter.(hash) in
    let rec valeur = function
      | (id, id', v) :: _ when id = unique a && id' = unique b -> v
      | _ :: q -> valeur q
      | _ -> raise Absent
    in valeur seau

let rec inter a b =
  if unique a = unique b then a
  else if unique a > unique b then inter b a
  else
    try
      trouveInter a b
    with
    | Absent ->
      match a,b with
        | Zero, _ -> Zero
        | Un, Un  -> Un
        | Un, Comb(_, _, b1, _) ->
          let c = inter Un b1 in
          ajouteInter a b c; c
        | Comb(_, i, a1, a2), Comb(_, j, b1, b2) when i=j ->
          let c =
            let temp = inter a2 b2 in
            if unique temp = 0 then inter a1 b1
            else cons i (inter a1 b1) temp in
          ajouteInter a b c; c
        | Comb(_,i,a1,_),Comb(_,j,_,_) when i<j ->
          let c = inter a1 b in
          ajouteInter a b c; c
        | Comb(_,i,_,_),Comb(_,j,b1,_) when i>j ->
          let c = inter b1 a in
          ajouteInter a b c; c
        | _ -> failwith "Erreur Intersection"


(* ________________ *)
(* Fonction Colonne *)
(* On commence par construire l'arbre des singletons correspondants aux dominos recouvrant la case, puis on ajoute les autres valeurs une par une en partant de la dernière *)

let domino j = (* la liste des dominos couvrant la case *)
    let rec aux acc = function
        | -1 -> acc
        | k -> if m.(k).(j) then aux (k::acc) (k-1) else aux acc (k-1)
    in aux [] (n-1)


let rec singletons = function (* l'arbre des singletons *)
    | [] -> Zero
    | a::q -> cons a (singletons q) Un

let rec ajout k a = match a with (* l'ajout d'un élément *)
    | Zero -> Zero
    | Un -> cons k Un Un
    | Comb(_,i,_,_) when k<i -> cons k a a
    | Comb(_,i,a1,a2) when k>i -> cons i (ajout k a1) (ajout k a2)
    | _ -> failwith "Erreur Ajout"

let colonne j = (* la construction de l'arbre complet *)
    let d = domino j in
    let s = singletons d in
    let rec aux acc = function
        | -1 -> acc
        | k when List.mem k d -> aux acc (k-1)
        | k ->  aux (ajout k acc) (k-1)
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
  let arbre, t_constr = chrono fonction_pavage () in
  let card, t_card = chrono cardinal arbre in
  printf "Nombre de pavages possibles : %i\n" card;
  printf "Temps de construction : %.2fs\n" t_constr;
  printf "Temps de calcul du cardinal : %.2fs\n" t_card;
  printf "Nombre d'arbres distincts construits : %i\n" !id_unique;
  stats_table tableArbre "Arbre";
  stats_table tableInter "Inter";
  stats_table tableCardinal "Card"


let () =
  Gc.set {(Gc.get ()) with Gc.space_overhead = 400};
  if execute_classique then begin
    affiche pavage "Colonne par colonne";
    id_unique := 2;
    let reinit t =
      let n = Array.length t in
      Array.blit (Array.make n []) 0 t 0 n in
    reinit tableArbre; reinit tableInter; reinit tableCardinal;
    Gc.full_major ()
    end;
  affiche pavage2 "\"Diviser pour régner\""
