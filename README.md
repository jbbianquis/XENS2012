# XENS2012
*Pavages d'un échiquier avec des dominos 2x1*

La version «packed» nécessite le package zarith, installable par OPAM (il faut installer gmp d'abord). Ça sert juste à calculer les cardinaux quand ils ne rentrent plus dans un int, il suffit de modifier légèrement le code pour virer la dépendance (les résultats deviennent faux à partir de p = 14).

La version «maxime» est celle postée par Maxime Rebout sur la liste UPS, la dernière version est une ré-écriture partielle de celle-ci (au fur et à mesure de ma lecture du code...).

Les résultats dans les fichiers texte sont obtenus après compilation «brutale» (-nossart -unsafe -O3). Pas assez de mémoire sur ma VM pour p=20, ça passe *peut-être* avec 16 Go (pas sûr, on a peut-être besoin de plus de 2^26 arbres distincts).
