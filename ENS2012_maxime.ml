(* ******************* *)
(* Constantes globales *)
(* ******************* *)
let p = 8;; (* Taille de l'échiquier *)
let cste = 19;; (* pour la fonction de hachage *)
let h = 19997;; (* taille de la table de hachage *)
let n = p*(p-1)*2;; (* possibilités de placer un domino *)

(* ******************* *)
(* Références globales *)
(* ******************* *)
let case = ref 0;; (* case de l'échiquier *)
let id_unique = ref 2;; (* pour identifier les arbres *)


(* Les types utilisés *)
type unique = int;;
type ac = Zero | Un | Comb of unique * int * ac * ac



(* Pour parcourir l'échiquier en diagonale *)
let case_suivante () =
  if !case mod p = 0 && !case/p < p-1 then case := !case/p + 1
  else
    begin
    if !case/p = p-1 then case := p*((!case mod p)+2)-1
    else case := !case + (p-1)
    end;;

(* Construction de la matrice de booléens *)
let m  = let t = Array.make_matrix n (p*p) false and ligne = ref 0 in
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
  t;;


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
let tableArbre = Array.make h []
let ajouteArbre a =
    let hash = hache(a) in
    tableArbre.(hash) <- a::tableArbre.(hash)
let presentArbre a =
    let seau = tableArbre.(hache a) in
    let rec recherche = function
        | [] -> false
        | c::q -> (egal c a) || recherche q
    in recherche seau
let trouveArbre a =
    let seau = tableArbre.(hache a) in
    let rec valeur = function
        | c::_ when (egal c a) -> c
        | _::q -> valeur q
        | _ -> failwith "Absent"
    in valeur seau

let cons i a1 a2 =
    if presentArbre (Comb(0,i,a1,a2)) then trouveArbre (Comb(0,i,a1,a2)) else
    let c = match (a1,a2) with
      | Comb(_,j,_,_),Comb(_,k,_,_) when i<j && i<k -> Comb(!id_unique,i,a1,a2)
      | _,Comb(_,k,_,_)  when i<k -> Comb(!id_unique,i,a1,a2)
      | Comb(_,j,_,_),Un when i<j -> Comb(!id_unique,i,a1,Un)
      | Zero,Un-> Comb(!id_unique,i,Zero,Un)
      | Un,Un  -> Comb(!id_unique,i,Un,Un)
      (* | Zero,Comb(_,k,_,_) when i<k -> Comb(!id_unique,i,Zero,a2) *)
      | _,_ -> print_int i; failwith "Erreur Construction"
    in incr id_unique; ajouteArbre c; c;;


(* _________________ *)
(* Fonction Cardinal *)
let tableCardinal = Array.make h [];;

let ajouteCard a v =
    let hash = hache(a) in
    tableCardinal.(hash) <- (unique a,v)::tableCardinal.(hash)
let presentCard a =
    let seau = tableCardinal.(hache a) in
    let rec recherche = function
        | [] -> false
        | c::q -> fst c = unique a || recherche q
    in recherche seau
let trouveCard a =
    let seau = tableCardinal.(hache a) in
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
        end;;

(* ______________ *)
(* Fonction Inter *)
let tableInter = Array.make h [];;

let ajouteInter a b v =
    let hash = (hache a)*(hache b) mod h in
    let seau = tableInter.(hash) in
    tableInter.(hash) <- ((unique a,unique b),v)::seau;;
let presentInter a b =
    let hash = (hache a)*(hache b) mod h in
    let seau = tableInter.(hash) in
    let rec recherche = function
      | [] -> false
      | c::q -> fst (fst c) = unique a && snd (fst c) = unique b || recherche q
    in recherche seau
let trouveInter a b =
    let hash = (hache a)*(hache b) mod h in
    let seau = tableInter.(hash) in
    let rec valeur = function
      | c::_ when fst (fst c) = unique a && snd (fst c) = unique b -> snd c
      | _::q -> valeur q
      | _ -> failwith "Absent"
    in valeur seau

let rec inter a b =
  if unique a = unique b then a
  else begin
    if unique a > unique b then inter b a
    else begin
      if presentInter a b then trouveInter a b
      else begin
        let c = match a,b with
          | Zero,_ -> Zero
          | Un,Un  -> Un
          | Un,Comb(_,_,b1,_) -> inter Un b1
          | Comb(_,i,a1,a2),Comb(_,j,b1,b2) when i=j ->
              let temp = inter a2 b2 in
                if unique temp = 0 then inter a1 b1
                else cons i (inter a1 b1) temp
          | Comb(_,i,a1,_),Comb(_,j,_,_) when i<j -> inter a1 b
          | Comb(_,i,_,_),Comb(_,j,b1,_) when i>j -> inter b1 a
          | _ -> failwith "Erreur Intersection"
        in ajouteInter a b c; c
        end
      end
  end;;


(* ________________ *)
(* Fonction Colonne *)
(* On commence par construire l'arbre des singletons correspondants aux dominos recouvrant la case, puis on ajoute les autres valeurs une par une en partant de la dernière *)

let domino j = (* la liste des dominos couvrant la case *)
    let rec aux acc = function
        | -1 -> acc
        | k -> if m.(k).(j) then aux (k::acc) (k-1) else aux acc (k-1)
    in aux [] (n-1);;

let rec singletons = function (* l'arbre des singletons *)
    | [] -> Zero
    | a::q -> cons a (singletons q) Un

let rec ajout k a = match a with (* l'ajout d'un élément *)
    | Zero -> Zero
    | Un -> cons k Un Un
    | Comb(_,i,_,_) when k<i -> cons k a a
    | Comb(_,i,a1,a2) when k>i -> cons i (ajout k a1) (ajout k a2)
    | _ -> failwith "Erreur Ajout";;

let colonne j = (* la construction de l'arbre complet *)
    let d = domino j in
    let s = singletons d in
    let rec aux acc = function
        | -1 -> acc
        | k when List.mem k d -> aux acc (k-1)
        | k ->  aux (ajout k acc) (k-1)
    in aux s (n-1);;

(* _______________ *)
(* Fonction Pavage *)
case := 0;; (* On repart de la première case *)
let pavage () =
    let arbre = ref (colonne 0) in
    for k = 1 to p*p-1 do
      case_suivante();
      arbre := inter !arbre (colonne !case);
    done;
    !arbre;;


(* ________________________ *)
(* Résultat et statistiques *)
let debut = Sys.time() in
  print_string "Nombre de pavages possibles : ";
  print_int(cardinal (pavage()));
  print_newline();
  print_string "Temps de calcul             : ";
  print_float(Sys.time() -. debut);
  print_string " s";
  print_newline();
  print_string "Nombre d'arbres construits  : ";
  print_int !id_unique;
  print_newline();
  print_string "Longueurs des seaux : ";
  print_newline();
  let borne = ref 0 in
  for k = 0 to h-1 do
    borne := max !borne (List.length (tableArbre.(k)))
  done;
  let seaux = Array.make (!borne+1) 0 in
  for k = 0 to h-1 do
    let l = List.length (tableArbre.(k)) in
      seaux.(l) <- seaux.(l)+1
  done;
  for k = 0 to !borne do
    print_string "   ";
    print_int k;
    print_string " : ";
    print_int seaux.(k);
    print_newline()
  done;;
