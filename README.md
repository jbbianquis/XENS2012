## Autour du sujet X-ENS 2012
*Pavages d'un échiquier avec des dominos 2x1*

La version «packed» nécessite le package zarith, installable par OPAM (il faut installer gmp d'abord). Ça sert juste à calculer les cardinaux quand ils ne rentrent plus dans un int, il suffit de modifier légèrement le code pour virer la dépendance (les résultats deviennent faux à partir de p = 14).

La version «maxime» est celle postée par Maxime Rebout sur la liste UPS, la dernière version est une ré-écriture partielle de celle-ci (au fur et à mesure de ma lecture du code...).

Les résultats dans les fichiers texte sont obtenus après compilation «brutale» (-nossart -unsafe -O3). Pas assez de mémoire sur ma VM pour p=20, ça passe *peut-être* avec 16 Go (pas sûr, on a peut-être besoin de plus de 2^26 arbres distincts).

Pour un traitement un peu moins brutal (solution polynomiale très jolie), se référer à http://www.math.cmu.edu/~bwsulliv/domino-tilings.pdf. On y trouvera même une forme close étonnamment simple !

![equation](http://latex.codecogs.com/gif.latex?T%282p%2C%202p%29%20%3D%20%5Cprod_%7Bi%20%3D%201%7D%5Ep%5Cprod_%7Bj%20%3D%201%7D%5Ep%5Cleft%284%5Ccos%5E2%5Cleft%28%5Cfrac%7Bi%5Cpi%7D%7B2p%20&plus;%201%7D%5Cright%29%20&plus;%204%5Ccos%5E2%5Cleft%28%5Cfrac%7Bj%5Cpi%7D%7B2p%20&plus;%201%7D%5Cright%29%5Cright%20%29)