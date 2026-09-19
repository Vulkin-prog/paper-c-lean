# Notes de formalisation pour le papier 3PREL8

Cette note concerne l'édition du 16 septembre 2026. Elle distingue les points
vérifiés, les précisions utiles pour une prochaine rédaction et les obligations
Lean encore ouvertes. Elle ne constitue pas une certification de l'ensemble
des nouveaux résultats.

## Points confirmés lors de l'extension

- **Annexe F.2, distance de couplage.** La borne de seconde différence par 1
  donne une borne en distance ℓ¹ entre deux configurations quelconques, pas
  seulement entre configurations comparables coordonnée par coordonnée. Le
  passage par leur minimum coordonnée par coordonnée est maintenant explicite
  en Lean. L'identité de Palm concerne la loi conditionnelle complète ; des
  covariances seules ne la remplacent pas.
- **Section 5, dictionnaires typiques.** L'espérance sur les dictionnaires reste
  extérieure à la probabilité sur les signes. L'identité des paires sélectionnées
  conserve le terme de collision et la distinction entre mots égaux et distincts.
  Le contrôle ancien du seul poids de recouvrement ne démontre pas ce nouveau
  théorème.
- **Section 6, information admissible.** L'optimiseur sous contrainte de
  mesurabilité est le maximum du seuil minimal admissible et du point de
  croisement. Optimiser sur un intervalle plus grand ne rend pas un événement
  mesurable dans une tribu plus petite.
- **Annexe F, pivot.** Le plus grand premier d'exposant impair a la valeur 1
  lorsque le support impair est vide. Son événement de sous-seuil est exactement
  le prédicat d'entier défectueux déjà utilisé par le comptage de Rankin ; le
  nombre 0 est exclu de la population comptée.

## Dépendances à garder visibles

L'ordre du papier est essentiel : queue scalaire indépendante, forçage exact,
comparaison microscopique, puis conséquences empiriques et déficit de Palm.
Aucune conséquence de l'annexe G ne doit être utilisée pour démontrer l'annexe F.

Le code réutilise les hypothèses de littérature explicites de la formalisation
antérieure. En particulier, la preuve finie de Palm utilise la solution de Stein
avec borne de Hessienne déjà déclarée. La construction analytique du semi-groupe
donnée dans le texte n'est pas pour autant entièrement reconstruite en Lean.
Cette limite devra rester explicite dans la future description de couverture.

Aucune erreur mathématique nouvelle du manuscrit n'a été établie à ce stade.
Les extensions arithmétiques et asymptotiques indiquées comme ouvertes dans la
[correspondance](FORMALIZATION_COVERAGE_V3PREL8.md) ne doivent pas être présentées
comme des corrections du papier, ni comme des résultats formalisés.

## Forçage arithmétique et voisinages dirigés — deuxième lot

Les points suivants sont maintenant vérifiés dans le modèle de signes premiers
existant, et ne reposent plus seulement sur une construction abstraite par blocs.

- **Simplification des hypothèses assurant le caractère privé des pivots (F.7).**
  Un premier sélectionné dont la valuation est impaire donne une coordonnée
  égale à 1 dans le vecteur de parité. Il suffit qu'il dépasse le diamètre de la
  fenêtre pour qu'il ne divise aucun autre sommet. Ni une valuation exactement
  égale à 1, ni une borne quadratique sur la taille des sommets n'est nécessaire.
  Ceci simplifie cette étape de preuve ; cela ne justifie pas de supprimer la
  condition plus forte sur `Y` dans le théorème microscopique complet, où elle
  intervient aussi dans les estimations de paires.
- **Distinguer support maximal et mot effectivement forcé (F.7).** Pour la
  marque `(e,σ)`, on impose les `L+e+2` valeurs brutes, frontières comprises.
  Les pivots supplémentaires du support maximal servent à majorer le voisinage
  des changements ; les forcer aussi imposerait un événement plus fort.
  La version Lean respecte cette distinction. Il serait utile de préciser la
  plage de l'indice dans la formule de remplacement des bits du manuscrit.
- **Convention de position.** Le bord gauche `j` du compagnon correspond au
  début de plage `j+1` du modèle déjà formalisé. Le signe est celui du premier
  point intérieur ; les deux frontières portent le signe opposé. Cette
  correspondance est vérifiée explicitement, ainsi que la masse `2^(-L-e-2)`.
- **Loi conditionnelle complète, même après un événement de petits premiers.**
  Le forçage est testé contre toute fonction de l'affectation complète des
  signes. Il donne donc la bonne loi jointe, pas seulement les marginales.
  La preuve couvre un événement arbitraire de probabilité positive déterminé par
  les petits premiers, et pas uniquement une affectation fixée de ceux-ci.
  Une identité pondérée fournit aussi la version algébrique pour les biais doux.
- **Simplification de F.6.** Le comptage d'une divisibilité translatée donne
  `n/q+1` sans imposer de rapport entre le décalage et `q`. Pour la somme des
  inverses des pivots, l'injectivité de `j ↦ j+a` à chaque décalage suffit :
  sommer ensuite sur les décalages produit le facteur `Q+1`. Les deux bornes
  finies de F.6 sont prouvées avec la véritable population des pivots.
- **Limite à conserver dans la présentation.** Un voisinage dirigé décrit des
  modifications possibles, avec un surcomptage des valuations paires. Ce n'est
  pas une nouvelle preuve d'indépendance à l'extérieur d'un graphe. Les bornes
  finies et le forçage exact ne dispensent pas de la somme réciproque asymptotique,
  des queues indépendantes et du bilan de comparaison final.

Ces observations sont des précisions et simplifications de preuve. Aucune
nouvelle erreur mathématique du manuscrit n'a été démontrée dans ce lot.
Les sources et PDF livrés par l'auteur restent inchangés.

## Enveloppe, somme réciproque et borne dirigée — troisième lot

Les estimations F.4, F.5 et F.6 sont maintenant démontrées sous forme de bornes
uniformes avec un paramètre d'erreur positif arbitraire. Le théorème des nombres
premiers reste l'entrée de littérature explicite déjà utilisée auparavant.
Aucune estimation de somme réciproque n'est ajoutée comme hypothèse.

- **Simplification de F.4.** On peut prouver l'inégalité de tangente directement
  dans le paramètre `u`. La dérivée de `D_param(t)-u*nu(t)` est
  `exp(t)*(t-1)*(t-u)/t²` : elle change de signe au bon endroit. Cette preuve
  évite de dériver la fonction inverse et traite aussi l'extrémité de la branche.
  Elle ne remet pas en cause la preuve par convexité du texte.
- **Précision de l'erreur.** La perte de l'enveloppe est majorée explicitement
  par `nu*r(u)`, où `r(u)` tend vers zéro et est finalement au plus `2/u`.
  Cela vérifie la précision `O(nu/u)` du papier, et pas seulement une erreur
  négligeable devant `V`. Le seuil est choisi avant la largeur libre `w`.
  Il ne faut pas remplacer cette étape par une équivalence au premier ordre.
- **Arrondi et décalage des tranches de F.5.** Pour un pivot entier,
  `kappa > floor(exp(w))` équivaut exactement à `kappa > exp(w)`.
  La tranche suivante utilise le comptage à `exp(w+1)` : ce décalage produit
  un facteur `exp(1)`, conservé dans la borne finie avant absorption. Le nombre
  de tranches et la queue résiduelle sont également conservés explicitement.
- **Simplification pour les supports élargis.** À hauteur de référence `log M`,
  le paramètre de Rankin positif permet de majorer le comptage jusqu'à tout
  `X >= M` sans remplacer `log X` par `log M` dans un reste asymptotique.
  L'augmentation de `X` améliore directement le terme exponentiel normalisé.
  Le support effectif `X=M+E_*+1` est dans ce cas.
- **Renforcement uniforme de la borne réciproque.** Par monotonie de la somme
  et absorption d'un facteur au plus 2, la borne finale est démontrée pour
  tous les entiers `X` tels que `2X >= M`, avec le même seuil en `M`.
  Cela couvre notamment `X=M+O(log M)`, y compris les décalages négatifs.
  C'est une possibilité de simplification de la formulation de F.5, sans
  nécessité de modifier les applications du papier.
- **Uniformité de F.6.** Pour un coefficient fixe `beta > 0`, le facteur lié
  à `Q <= beta*log M` est absorbé à l'échelle `nu`. La borne obtenue est
  `n²*exp(-2V+epsilon*nu)+n*(Q+1)²`, uniformément avant le choix du bon ensemble
  et des pivots. Les conditions géométriques `Q <= n` et `M <= 2(n+Q)` restent
  explicites ; elles correspondent au régime asymptotique utilisé par le texte.

Aucune nouvelle erreur mathématique du manuscrit n'a été identifiée. Ces
résultats ferment le bloc d'estimations analytiques et arithmétiques nécessaire
au voisinage dirigé ; ils ne constituent pas encore la comparaison de Poisson
microscopique. Le bilan de Palm, les queues indépendantes et le raccord complet
au champ conditionné restent à assembler. Les fichiers du manuscrit sont inchangés.

## Champ complet, coûts de Palm et source infinie — quatrième lot

Le raccord du modèle est désormais explicite : le bon ensemble `G0` conserve
les frontières gauches de `1` à `n`, avec `j+1 >= ceil(sqrt M)`, puis toutes les
marques de longueur autorisée et les deux signes. Le forçage fournit exactement
la loi de ce vecteur conditionnée par la marque, sous tout événement de petits
premiers de probabilité positive. L'égalité avec les masses conditionnelles de
la source infinie est démontrée par restriction au cylindre commun.

- **Préciser la taille du cylindre.** Le dernier sommet observé peut dépasser
  l'extrémité de la plage des départs. Il faut couvrir tous les sommets marqués,
  ainsi que tous les premiers jusqu'à `Y` pour représenter l'intégralité de
  l'environnement conditionnant. La notation du cylindre ne doit pas être
  confondue avec l'extrémité `M` de l'observation.
- **Regrouper avant de majorer.** La contribution du même site est exactement
  le carré de la somme des taux de ses catégories. Les produits entre sites
  ont la même structure. La somme des taux géométriques est au plus `2^-L` ;
  aucun facteur égal au nombre de catégories n'est nécessaire. La simplification
  est démontrée sans supposer d'indépendance extérieure au voisinage dirigé.
- **Renforcement du traitement local.** La majoration locale par quatre fois
  le produit des taux est vraie sur chaque fibre des petits premiers. Une
  identité de mélange permet de la conserver sous tout événement de ces
  premiers, sans payer un facteur `exp(I)` à cette étape. Le facteur global
  du bilan du papier reste une majoration valide, mais moins précise localement.
- **Garder le rang de toutes les valeurs pour les paires éloignées.** La borne
  par rang est inconditionnelle. Sa version conditionnelle paie une seule
  fois l'inverse de la masse de l'événement. Il serait incorrect de la lire
  comme une estimation uniforme sur chaque affectation des petits premiers.
  Les preuves Lean rendent cette différence visible dans les hypothèses.
- **Simplification et renforcement de F.3.** La bande exacte `V-2..3V+2` est
  incluse dans une bande multiplicative fixe pour `V` assez grand. Le passage
  du plafond `X` à `max(M,X)` coûte au plus deux si `M <= 2X`, puis `log 2`
  s'absorbe à l'échelle `nu`. Cela donne l'énoncé pour tous ces plafonds avec
  un même seuil, sans devoir développer `log X = log M + o(1)`.
- **Distinguer comparaison finie et limite finale.** La comparaison du champ
  conservé de la source infinie est établie avec des coûts arithmétiques explicites.
  Pour revendiquer 7.7, il reste les queues indépendantes, les sites supprimés,
  la somme de l'excès de relations et la conclusion asymptotique uniforme.
  Ces obligations ne sont pas remplacées par des hypothèses de convergence.

Aucune nouvelle erreur mathématique du manuscrit n'a été démontrée dans ce lot.
Les points ci-dessus sont des clarifications ou des simplifications ; les
sources et PDF livrés restent inchangés. F.3 et F.7 sont désormais renseignés
comme prouvés avec leurs périmètres précis dans la correspondance. L'ensemble
du réalignement 3PREL8 n'est toujours pas terminé.


## Queues indépendantes et positions écartées — cinquième lot

- **Simplification de la queue indépendante de F.1.** La borne du premier
  moment déjà établie pour un masque arbitraire suffit : l'existence d'une
  marque d'excès strictement supérieur à `E` implique un départ ordinaire de
  longueur `L+E+1`. Une borne d'union donne directement `card(mask)/2^(L+E+1)`
  plus le reste microscopique, sans recourir à la comparaison scalaire de
  Stein. La voie par cette comparaison est également formalisée, mais donne
  des constantes moins bonnes. Les deux preuves sont indépendantes du nouveau
  théorème microscopique ; il n'y a pas de dépendance circulaire.
- **Conserver la marge d'une unité.** La bande logarithmique porte sur le
  nombre de lignes augmenté de un. Pour la queue, c'est donc `L+E+2`, alors
  que le taux de départ est `2^-(L+E+1)`. Les deux signes sont déjà réunis
  dans l'événement de longueur exacte et ne coûtent aucun facteur deux.
- **Uniformité avant le conditionnement.** Le seuil commun précède le masque
  et l'événement de conditionnement. Pour tout événement de probabilité
  positive, l'intersection coûte au plus l'inverse de cette probabilité.
  Cette étape ne requiert même pas que l'événement dépende des petits premiers.
- **Coordonnées des positions écartées.** Le complément de `G0` est un ensemble
  de frontières gauches `j`, tandis que la borne de départ s'applique à `j+1`.
  La translation est injective. Le nombre supprimé est au plus
  `ceil(sqrt M) + card(badPivotSites)`, d'où une borne directe de sa probabilité
  conditionnelle. Ce mauvais ensemble inclut aussi les sites peu profonds :
  il majore donc celui du papier, restreint aux sites profonds. Le plafond
  est conservé exactement, sans approximation.
- **Ne pas confondre la borne intermédiaire avec la limite.** Il reste à montrer
  que le choix informationnel de `E` appartient à la bande décalée, à majorer
  le nombre de mauvais pivots et à absorber tous les restes. L'inégalité
  algébrique donnant une queue de masse au plus `exp(-V)` est démontrée sous
  sa condition explicite ; la satisfaction de cette condition par le choix
  final du papier ne doit pas être présumée.

Ces points sont des simplifications et des précisions de preuve, pas des
corrections d'erreurs établies. Les fichiers sources et PDF du manuscrit restent
inchangés. Le théorème 7.7 et l'ensemble du réalignement ne sont pas encore clos.


## Mauvais supports et séparation des relations — sixième lot

- **Compter les décalages, puis absorber leur nombre.** À décalage fixé, la
  translation du bord gauche vers le sommet est injective. Le nombre de
  mauvais supports est donc au plus `(Q+1)*card(pivotValues(n+Q,Y))`.
  La borne de population au point selle et l'absorption du facteur logarithmique
  donnent `n*exp(-V+epsilon*nu)`, uniformément sous les conditions explicites
  `M <= 2(n+Q)`, `Q <= n` et `Q <= beta*log M`. Cela reste valable pour notre
  ensemble incluant les sites peu profonds, donc aussi pour celui du papier.
- **Budget d'information.** L'inégalité `log(lambda)-log(a) <= V-c*nu`
  entraîne directement `lambda*exp(-V+epsilon*nu)/a <= exp(-(c-epsilon)*nu)`.
  Cette absorption est désormais prouvée séparément ; la positivité de
  l'intensité et de la masse conditionnante y reste explicite.
- **N'étendre aux paires éloignées que l'excès de relations.** Écrire
  `2^rho = 1+(2^rho-1)` avant de sommer permet de garder le terme `1` sur
  le graphe dirigé. Seul l'excès, non négatif, s'étend à toutes les paires
  séparées. Étendre également le terme constant ferait perdre la borne
  recherchée en introduisant un coût quadratique inutile.
- **Coût local sans facteur de catégories.** Un voisinage entier de rayon
  `Q` contient au plus `2Q+1` sites. La contribution locale obtenue est au
  plus `4*card(G)*(2Q+1)`, sans facteur lié au nombre de marques ou de signes.
  Cette borne légèrement large suffit pour le régime asymptotique ; elle
  conserve l'exclusion de la diagonale dans le graphe effectif.

Le bilan ainsi obtenu porte sur le champ conditionné de la source infinie.
Il reste à y substituer le profil arithmétique de l'excès de relations et à
vérifier toutes les conditions du choix informationnel des paramètres.
Aucune erreur nouvelle du manuscrit n'est affirmée et ses fichiers sont inchangés.


## Profil complet et cutoff informationnel exact — septième lot

- **Identification du profil, sans changement de noyau.** Le rang du système
  joint à `L+E+2` valeurs est exactement celui du profil préexistant à hauteur
  `Q=L+E+1`. La translation `j -> j+1` conserve les distances et les paires
  ordonnées. L'excès réel est aussi exactement la conversion du poids naturel
  `2^rho-1`, car ce dernier ne subit aucune troncature à zéro.
- **Intervalle fermé et cylindre.** Les départs conservés appartiennent à
  `[ceil(sqrt M),M]` lorsque `n+1 <= M`. La borne de profil est appliquée sur
  cet intervalle fermé, dans un cylindre contenant tous les sommets requis.
  Agrandir ce cylindre ne change pas le rang ; aucune restriction de parité
  n'est introduite.
- **Cutoff exact.** Pour `E=ceil((I+V+log(2+lambda))/log 2)`, on a
  `2^E >= exp(I+V)*(2+lambda)` et donc
  `exp(I)*lambda/2^(E+1) <= exp(-V)/2`. Le facteur `1/2` améliore la borne
  affichée sans être nécessaire à son application.
- **Contrôle explicite de l'arrondi.** Sous `I >= 0`, `lambda >= 1` et
  `I+log(lambda) <= V`, l'inégalité `log(2+lambda) <= log(lambda)+log 3`
  donne `E*log 2 <= 2V+log 3+log 2`. Ainsi
  `2^(2E+2) <= 144*exp(4V)`. Cette borne suffit à absorber l'allongement du
  profil dans toute puissance positive de `M`, uniformément avant `I` et
  `lambda`, et à conserver une bande logarithmique fixe.
- **Le conditionnement reste absorbable.** Le même budget donne
  `exp(I)*(lambda^2+2lambda) <= 3*exp(2V)`. Le terme total de relations,
  après multiplication par `exp(I)`, est donc au plus `M^(-1/3+epsilon)`
  pour tout `epsilon > 0`, avec un seuil uniforme dans les paramètres admis.
- **Distinguer les deux intensités.** Le cutoff utilise `lambda=M*2^-L`,
  tandis que le budget du papier utilise `Lambda=(M-L)*2^-L`. Leur proximité
  dans le régime considéré est attendue, mais le passage d'un budget à l'autre
  doit être prouvé en utilisant la marge d'information. La présente borne
  du profil conserve explicitement le budget ambiant comme hypothèse.

Ces résultats ferment la contribution arithmétique des relations sous les
hypothèses indiquées. Ils ne ferment pas encore l'ensemble de 7.7 : restent
notamment le raccord des budgets, les conditions géométriques et l'assemblage
uniforme des autres restes. Aucune erreur nouvelle du manuscrit n'est affirmée ;
les sources et PDF livrés sont inchangés.


## Assemblage uniforme du champ microscopique — huitième lot

- **Deux intensités, une marge stricte.** Lorsque `L=O(log M)`, on a
  `(M-L)*2^-L <= M*2^-L <= 2*(M-L)*2^-L` pour M assez grand.
  Le coût logarithmique est donc au plus `log 2`. Pour `c' < c`, la divergence
  de `nu` absorbe ce coût dans `(c-c')*nu`. Le budget du manuscrit donne bien
  le budget ambiant nécessaire au cutoff. Il n'est pas nécessaire de remplacer
  le budget du papier par une hypothèse plus forte.
- **Géométrie dérivée.** Un cylindre `C=2M+(L+E+2)` couvre à la fois les
  valeurs observées et tous les petits premiers. Le budget assure la bande
  logarithmique allongée, le support court et `2*(L+E+2) <= Y`. Ces propriétés
  sont désormais des conclusions, avec un seuil commun avant L et I.
- **Restes réellement conditionnés.** La suppression des sites coûte au plus
  `3*exp(-c'*nu)+M^(-1/3+epsilon)` pour la source ; sa cible coûte au plus
  `exp(-c'*nu)+M^(-1/3+epsilon)`. La queue des excès de la source est au plus
  `3*exp(-c'*nu)`. Les probabilités sont celles des événements réels divisées
  par la vraie masse de conditionnement. Aucun argument d'indépendance avec
  cet événement n'est introduit.
- **Décalage sans perte.** Le passage des bords gauches j aux départs j+1
  est une bijection conservant les marques. Les lois conditionnelles et les
  produits de Poisson correspondent exactement ; leur variation totale est
  identique. Les queues sont ensuite retirées sur les espaces probabilisés
  effectifs, puis tous les sites intérieurs sont restaurés.
- **Constante explicite facultative.** L'assemblage donne
  `10*exp(-c'*nu)+4*M^(-1/3+epsilon)`. Ces constantes n'ont pas été optimisées ;
  elles suffisent à la notation asymptotique de 7.7. Il n'est pas nécessaire
  de les ajouter au manuscrit. La convergence est prouvée pour les suites
  satisfaisant la bande et le budget explicites, sans supposer la comparaison
  finale. Toute lecture mesurable conserve la borne.

Le raccord spécifique avec `floor(log_2 M)-a_M` est désormais prouvé :
`a_M/log M -> 0` implique une bande logarithmique fixe et rend la soustraction
naturelle légitime pour M assez grand. La divergence de Lambda donne aussi
Lambda >= 1 à partir d’un certain rang.

Ces preuves gardent les entrées analytiques et arithmétiques déjà déclarées
par le dépôt, notamment la solution analytique de Stein de F.2. La restriction
dyadique et la clause de noyau de Markov restent à expliciter, ainsi que les
familles encore ouvertes dans le registre. Les remarques de ce lot sont des
clarifications et simplifications ; elles ne signalent pas une nouvelle erreur
dans le papier. Les sources et PDF de l'auteur restent inchangés.


## Restriction dyadique et noyaux de Markov — neuvième lot

- **Simplification de la preuve dyadique.** Pour deux hauteurs logarithmiques
  admissibles `H <= K`, l'équation de selle croissante donne directement
  `V(H) <= V(K)` et `nu(H) <= nu(K)`. Puis `nu=H/V` donne
  `nu(K) <= (K/H)*nu(H)`. À `K=H+log 4`, cela suffit à obtenir
  `nu(K) <= (1+delta)*nu(H)` pour tout delta positif à partir d'un certain rang.
  La différentiation implicite et l'estimation `V'(H)=O(1/nu)` ne sont donc pas
  nécessaires au corollaire dyadique. Cette preuve de remplacement ne prétend
  pas démontrer cette estimation de dérivée, plus forte.
- **Marge d'information.** Si `0<a<c`, la monotonie et la borne précédente
  absorbent tout coût logarithmique constant B dans la différence entre
  `V(H)-c*nu(H)+B` et `V(H+log 4)-a*nu(H+log 4)`. Le rapport des intensités
  dyadique et préfixe est compris entre 1 et 4 lorsque L<=N. Prendre B=log 4
  suffit. La décroissance de l'erreur exponentielle suit directement de la
  monotonie de nu ; aucun paramètre intermédiaire supplémentaire n'est requis.
- **Même conditionnement, mêmes positions.** La monotonie du cutoff implique
  `F_{Y_N} <= F_{Y_{4N}}`. L'événement de départ reste cependant soumis à
  `F_{Y_N}` dans l'énoncé final. Les positions `[N,2N)` sont exactement des
  positions du préfixe à 4N. La restriction du champ source et de la cible est
  exacte, sans translation de grille ni restriction de la longueur complète.
- **Constante unitaire pour les noyaux.** Centrer une fonction à valeurs dans
  `[0,1]` en lui soustrayant `1/2` transforme la borne signée `2*||f||∞*TV`
  en la borne `TV` du corollaire 7.8. Cette méthode évite ici l'intégration des
  ensembles de niveau. La normalisation des deux probabilités est utilisée
  explicitement. Tout noyau de Markov commun, suivi éventuellement d'une
  application mesurable, conserve donc la borne, sans hypothèse de continuité.

Le corollaire dyadique est maintenant relié à sa normalisation exacte et à son
budget à un seul facteur d'intensité. Les mêmes prémisses analytiques et
arithmétiques explicites que pour le préfixe subsistent. Ces observations sont
des simplifications possibles de rédaction, pas le signalement d'une nouvelle
erreur. Les fichiers du manuscrit restent inchangés.


## Fréquences empiriques et fenêtres recouvrantes — dixième lot

- **Constante exacte de variance.** Pour une fenêtre de longueur `h>0`, au
  plus `2h-1` origines ont une fenêtre qui la rencontre, diagonale comprise.
  La covariance des autres indicatrices est nulle par indépendance des
  coordonnées sous la cible produit. La borne `Cov(X,Y)<=1/4` suffit pour
  sommer : on peut l'obtenir de `Var(X-Y)>=0` et des deux bornes
  `Var(X),Var(Y)<=1/4`. Il n'est pas nécessaire de démontrer une borne sur
  la valeur absolue de chaque covariance. Cela donne exactement
  `Var(F_r)<=(2h-1)/(4N)`, y compris aux bords (où il y a moins de voisins).
- **Centrage et fenêtres contenues.** La variance seule reste valide pour
  des fenêtres tronquées. En revanche, le centrage commun par la masse
  `Poisson(h*p){r}` utilise explicitement le fait que chaque fenêtre contient
  exactement h sites, soit `N+h<=n+1` dans l'indexation finie. Pour le papier,
  `N=n-h+1` et il faut se placer à un rang où `1<=h<=n`. Les premiers rangs
  dégénérés peuvent être écartés dans un énoncé asymptotique ; ils ne doivent
  pas être normalisés comme des probabilités si N=0.
- **Un seul transfert de probabilité.** L'événement
  `|F_r-Poisson(h*p){r}|>eta` est une seule partie mesurable de l'espace du
  champ. Sa probabilité source est bornée par `Delta+(2h-1)/(4N*eta^2)`.
  Aucun facteur N ne multiplie Delta, et aucune indépendance des fenêtres
  recouvrantes n'est invoquée. Ce point de la preuve du papier est confirmé.
- **Indexation et terminaison.** La coordonnée finie i est le départ entier
  `i+2`. Une fenêtre d'origine u correspond donc exactement aux termes
  `J_{j+1,L}` avec `j=u+1,...,u+h`. La somme de toutes les marques signées et
  de tous les excès coïncide presque sûrement avec l'indicatrice de départ,
  grâce à la terminaison des plages. Ce passage est une égalité presque
  sûre, et non une identité requise pour chaque réalisation exceptionnelle.
- **Arrondi et limite de Poisson.** Pour `p>0` et `tau>=0`, la fenêtre
  `h=floor(tau/p)` satisfait `0<=tau-h*p<p`. Il suffit donc de montrer
  `p_k->0` pour identifier la moyenne limite ; la continuité de chaque
  masse de Poisson se lit directement dans sa formule explicite.
- **Convergence presque sûre.** Les fréquences sont des masses positives
  de somme un pour toute réalisation lorsque N>0. La sommabilité de Delta
  et de h/N donne celle de tous les événements d'écart, pour chaque entier
  r et chaque seuil `1/(m+1)`. Borel–Cantelli puis l'argument discret de
  Scheffé suffisent ; aucun couplage des cibles entre échelles ni contrôle
  uniforme supplémentaire des queues de la loi empirique n'est requis.

La sommabilité de l'erreur microscopique explicite sur `M_k=2^k` est
également démontrée. Il reste à appliquer les estimations de selle au choix
exact de `L_k` du corollaire 7.8a : admissibilité, budget d'information,
sommabilité de h/N et décroissance du taux par site. L'obstruction de support
pour le champ complet (7.8b) reste distincte et ouverte. Ces observations
confirment ou simplifient la preuve ; aucune nouvelle erreur du manuscrit n'a
été établie dans ce lot. Les fichiers du manuscrit restent inchangés.


## Corollaire empirique aux échelles exactes — onzième lot

- **Budget explicite sans développements plus fins.** Pour
  `M=2^k`, `d=floor(alpha*V/log 2)` et `L=k-d`, on obtient directement
  `exp(alpha*V)/2 <= 2^d <= exp(alpha*V)`. Dès que `L<=M/2`, l'intensité
  réelle satisfait donc `exp(alpha*V)/4 <= Lambda <= exp(alpha*V)`.
  Cela donne la divergence de Lambda pour alpha>0. Pour alpha<1, la seule
  propriété `nu/V -> 0` suffit à absorber tout terme fixe `c*nu` dans
  `(1-alpha)*V`. Les développements détaillés des deux selles, bien que
  corrects et informatifs, ne sont pas nécessaires à ce corollaire.
- **Rapports à distinguer.** Avec `n=M-L`, on a explicitement
  `h/n <= 4*tau*exp(-alpha*V)`. La sommabilité suit de `V>=nu` à partir
  d'un certain rang et de la sommabilité dyadique déjà établie de
  `exp(-alpha*nu)`. Puis `h/n -> 0` donne `2h<=n` éventuellement, d'où
  `n<=2N` et la sommabilité du véritable rapport h/N utilisé par Chebyshev.
  Cette transition justifie la comparaison implicite des deux dénominateurs
  dans la preuve du papier.
- **Arrondis et premiers indices.** La profondeur entière est o(log M),
  donc la soustraction `k-d` est légitime à partir d'un certain rang.
  La définition totale en entiers naturels adopte une extension arbitraire
  aux premiers indices ; `N=(n-h)+1` y reste positif. Lorsque la fenêtre
  tient dans les sites, elle coïncide exactement avec la définition du papier.
  Cette convention évite toute normalisation par zéro sans changer la limite.
- **Constantes pour la taille de la fenêtre.** La formalisation donne
  `(tau/2)*M*exp(-alpha*V) <= h <= 2*tau*M*exp(-alpha*V)` éventuellement.
  Avec `V/log M -> 0`, cela donne `log h/log M -> 1`. Ces deux conclusions
  justifient les deux formes de croissance affichées dans l'énoncé.
  L'identification de la moyenne limite utilise séparément l'arrondi exact,
  comme demandé par le paragraphe « Scope and comparison ».
- **Choix fixe de l'erreur sommable.** Dans l'application du théorème
  microscopique, on peut fixer c=2, c'=1 et epsilon=1/6, pour obtenir
  `10*exp(-nu_M)+4*M^(-1/6)`. Il n'est pas nécessaire de conserver ces
  paramètres auxiliaires dans l'énoncé final du corollaire empirique.

Le corollaire 7.8a est maintenant démontré pour chaque couple fixe
`0<alpha<1`, `tau>0`, sur les hauteurs dyadiques exactes. Ses conditions
numériques sont déduites des définitions ; les mêmes prémisses analytiques
et arithmétiques explicites que pour la comparaison microscopique subsistent.
Cela ne démontre ni un ensemble simultané pour tous les paramètres, ni une
convergence à toutes les tailles, ni l'obstruction de support 7.8b.
Aucune correction du manuscrit n'est imposée par ce lot ; les points ci-dessus
sont des précisions ou des simplifications de preuve. Ses fichiers restent
inchangés.


## Obstruction du champ empirique complet — douzième lot

La remarque 7.8b est maintenant démontrée, y compris la borne finie et
l'assertion `N*p^2=M^(-1+o(1))`, sans prémisse analytique ou arithmétique.
Aucune correction du texte n'est nécessaire. Les précisions suivantes
peuvent simplifier sa présentation ou rendre sa portée plus explicite.

- **Un argument déterministe général.** Pour toute loi empirique issue de
  N observations et toute cible Q, si les atomes d'un événement E ont une
  masse au plus b, alors `TV >= Q(E)-N*b`. Il suffit de tester E privé
  du support empirique. Les observations peuvent être répétées et ne sont
  soumises à aucune hypothèse d'indépendance. Cela explique directement
  pourquoi la conclusion vaut pour chaque réalisation fixée.
- **Le seuil de deux points.** Pour la cible de Poisson produit,
  `Q{|z|>=2}=1-exp(-h*p)*(1+h*p)` et `Q{z}<=p^2` sur cet événement
  lorsque p<=1. La borne individuelle résulte simplement de l'exponentielle
  au plus un, des factorielles au moins un, puis de `p^|z|<=p^2`.
- **La convergence du terme d'erreur suffit à l'obstruction.** On obtient
  directement `N*p^2 <= 2*exp(2*alpha*V)/M` à partir d'un certain rang,
  ce qui tend vers zéro puisque V=o(log M). L'égalité logarithmique plus
  précise affichée dans le papier est également formalisée :
  `log(N*p^2)/log M -> -1`. Elle suit de `M/4<=N<=2M` éventuellement
  et de `L*log 2/log M -> 1`.
- **Positions et normalisation exactes.** Avec des indices Lean commençant
  à zéro, la coordonnée relative i correspond au départ entier `u+i+2`,
  donc exactement à `J_{u+i+1,L}` pour l'indice i du papier commençant à un.
  La mesure empirique est l'image de l'origine uniforme ; la masse de tout
  événement est démontrée égale au nombre d'observations dans cet événement
  divisé par N. La convention aux premiers indices ne change pas la limite,
  et les fenêtres sont finalement toutes contenues, comme établi pour 7.8a.

Le corollaire 7.8a et la remarque 7.8b sont donc tous deux formalisés.
Seul le corollaire utilise les prémisses de comparaison microscopique déjà
répertoriées ; la remarque repose sur la taille du support et les échelles.
Les sources du manuscrit restent inchangées.


## Dictionnaires typiques et cutoff adapté à l'information — treizième lot

Le théorème 5.3 et la proposition 6.2 sont maintenant démontrés, sous les
prémisses AGG et PNT déjà déclarées dans le dépôt. Aucun résultat final de
comparaison ni aucune limite supplémentaire n'est supposé. Les sources du
manuscrit restent inchangées. Les observations suivantes peuvent simplifier
la rédaction ; elles ne constituent pas des erreurs dans ces énoncés.

- **Moyenner après la distance.** La sélection du dictionnaire doit rester
  extérieure à la distance conditionnelle. On majore la distance pour chaque
  dictionnaire fixé, puis on moyenne les coûts positifs. La suppression réelle
  moyenne vaut exactement `a*#bad` sur chaque fibre de petits premiers, quelle
  que soit sa loi arithmétique. C'est la justification précise de la disparition
  du défaut pondéré dans ce seul théorème.
- **Collisions et paires locales.** L'injection des relations des différences
  dans celles du système empilé est construite par `t -> (t,-t)` ; en
  caractéristique deux, c'est bien `(t,t)`. Le coût local peut être obtenu avec
  l'identité d'espérance du poids de recouvrement déjà démontrée, sans refaire
  le calcul des chaînes du graphe d'égalité. La borne finie obtenue est
  `2*a*D+8*a^2*#mask*B+6*a^2*edges+2*a*p*R`.
- **Un seul petit-o uniforme.** Prendre le supremum des véritables distances
  moyennes admissibles, augmenté de zéro si le régime est vide, définit un
  taux déterministe entre zéro et un. Les estimations pour toute marge fixe
  se convertissent en `C*(exp(-V+delta)+N^(-1/3+epsilon))` avec `delta/nu->0`
  au moyen d'une enveloppe logarithmique explicite. Cela évite de choisir un
  petit-o séparément pour chaque longueur ou taille. Une borne inférieure
  positive sur l'intensité n'est pas nécessaire pour cette comparaison.
- **Existence sans dérivation implicite.** Le cutoff adapté est construit
  sur l'intervalle des paramètres des selles dure et élargie, où la fonction
  est continue. La décroissance du coût de suppression donne ensuite unicité,
  optimum et amélioration stricte. Les formules de dérivées du compagnon ne
  sont donc pas nécessaires à ces conclusions et ne sont pas nouvellement
  formalisées dans ce lot.
- **Limite quadratique exacte.** Avec `u` le paramètre de la selle adaptée,
  `w^2+I*w=2*H*(u-normalizedEi(u))`. Encadrer `u` par les deux paramètres déjà
  étudiés suffit à obtenir la limite `(sqrt(theta^2+8)-3*theta)/4` du budget
  divisé par V. Aucune asymptotique de la nouvelle racine n'est postulée.
- **Troncature auxiliaire simplifiée.** Pour prouver la proposition 6.2,
  on peut réutiliser `E=3*ceil(Vhat/log 2)`, déjà certifié dans le dépôt.
  Le budget implique `I+log Lambda<=w<=Vhat`, d'où un coût de queue au plus
  `exp(-2*Vhat)` après conditionnement. Cette troncature reste `O(V)` et
  disparaît des lois finales. Le choix plus précis affiché dans le papier
  est valable mais n'est pas nécessaire à cette preuve.
- **Régime littéral.** La marge d'information et `Lambda>=1` impliquent la
  bande logarithmique utilisée par les estimations finies ; ce n'est pas une
  nouvelle hypothèse de la proposition. La comparaison finale conserve le
  même événement dans la sigma-algèbre complète à son cutoff adapté et donne
  la borne explicite `67*exp(-cprime*nu)+64*N^(-1/3+epsilon)`.

Le maximum algébrique sous une borne inférieure de cutoff prescrite est
également démontré pour la vraie selle. L'extension non numérotée de la
comparaison complète à ce cutoff contraint reste à assembler. Le corollaire
des dictionnaires affines et les compléments de Palm/cumulants restent ouverts.


## Dictionnaires affines et énoncé introductif — quatorzième lot

Le corollaire 5.4 et la partie nouvelle du théorème introductif 1.3 sont
maintenant démontrés, avec les prémisses AGG/PNT déjà déclarées. Le lot ajoute
67 théorèmes dans 15 modules. Les fichiers du papier restent inchangés.

- **Échantillonnage exact.** Le modèle formel tire uniformément une application
  linéaire surjective et un décalage indépendant. Une bijection explicite avec
  les matrices de rang plein du papier prouve l'égalité exacte des moyennes.
  On ne remplace donc pas ce modèle par un sous-ensemble uniforme de même taille.
- **Preuve des inclusions simplifiée.** L'action des changements de coordonnées
  est transitive sur les vecteurs non nuls. Le double comptage des noyaux de
  cardinal `2^(B-r)` donne directement la probabilité d'annuler un vecteur non
  nul. La moyenne sur le décalage donne ensuite les formules à un et deux mots.
  Il n'est pas nécessaire de compter les bases ordonnées des noyaux. Les cas
  `r=0` et `r=B` sont inclus ; la formule à deux mots distincts suppose `B>=1`.
- **Portée exacte de l'argument à deux moments.** L'égalité des probabilités
  d'inclusion transfère les coûts de suppression, de paires arithmétiques et
  de recouvrement. Elle ne prouve pas une égalité des distances moyennes des
  deux ensembles. La preuve borne d'abord chaque distance conditionnelle à
  dictionnaire fixé, puis moyenne sa borne positive. Cette distinction mérite
  de rester explicite dans la preuve du corollaire.
- **Un taux uniforme pour l'ensemble affine.** On construit son propre
  supremum des distances admissibles. Les estimations communes donnent ensuite
  le même type de petit-o uniforme. La proportion exceptionnelle est calculée
  sur les couples matrice/décalage effectivement tirés.
- **Deux distances dans l'introduction.** La convergence en probabilité est
  établie pour toute tolérance positive, tant vers le produit de Poisson
  qu'entre les deux champs réellement issus des modèles arithmétique et iid.
  Le terme supplémentaire est borné par `8*K^2*betaMax*log(N)/N`, ce qui rend
  son annulation uniforme explicite. Les restrictions déterministes contractent
  point par point, avant toute moyenne.
- **Exemple de description courte.** Si les écarts de B et r à leurs valeurs
  logarithmiques sont bornés par `CB` et `Cr`, le quotient `m/N` est compris
  entre `exp(-(CB+Cr)*log 2)` et `exp((CB+Cr)*log 2)`. Le coût exact est
  `r*B+r=r*(B+1)` bits, avec une borne explicite en `log(N)^2`. Ce sont des
  bornes sur les candidats aléatoires ; elles ne certifient pas une matrice
  particulière sans contrôler son erreur.

Aucune erreur nouvelle n'a été identifiée dans ces énoncés. Les remarques
ci-dessus précisent la portée du transfert et proposent une preuve plus
directe de l'échantillonnage. Les compléments de Palm/cumulants et la revue
finale des assertions non numérotées restent à traiter.


## Identités de Palm et normalisation — quinzième lot

Ce lot apporte 43 théorèmes dans huit modules. Il avance les résultats G.3
à G.6 sans les présenter comme entièrement terminés. Aucune prémisse de
littérature supplémentaire n'intervient et les sources du papier ne changent pas.

- **Présence et régularité sont deux preuves distinctes.** Pour une géométrie
  munie de premiers privés, la probabilité arithmétique de présence simultanée
  des mots signés est maintenant calculée exactement, sur chaque événement
  des petits premiers. La grande probabilité de cette régularité sous la cible
  reste à établir par les comptes de noyaux et de classes CRT. Une factorisation
  de présence seule ne donne pas une probabilité de configuration exacte.
- **Occurrences brutes indexées séparément.** Le système affine rassemble les
  couples (mot, position interne). Deux occurrences de la même valeur entière
  ne sont donc pas identifiées artificiellement ; leur répétition interdit
  bien la propriété de premier privé du papier.
- **Suppression ordinaire après sommation.** La probabilité conditionnelle de
  configuration, multipliée par celle de présence, redonne sa masse réelle.
  Les événements de configurations retenues distinctes sont disjoints. Leur
  somme paie exactement l'événement « configuration retenue régulière et départ
  à l'extérieur », majoré par le coût ordinaire de suppression. Aucun facteur
  exponentiel en l'intensité n'apparaît dans ce calcul.
- **Normalisation sans contrôle supérieur du rapport.** Pour b>0 et x>=0,
  la différence des parties positives de 1-bx et 1-x est au plus |log b|.
  La preuve est uniforme même lorsque x est grand. Pour le facteur
  exp(g*p)*(1-p)^(g-k), nous obtenons la pénalité explicite
  `k*p+g*p^2/(1-p)`. Cette borne, légèrement moins fine que le facteur 1/2
  affiché dans le papier, suffit à la même conclusion en grand O.
- **Ce qui reste à instancier dans G.4/G.5.** Le lemme dénombrable de comparaison
  conserve explicitement les identités de masses de configurations et le coût
  de projection. Il ne les remplace pas par une hypothèse finale de convergence.
  Leur raccord au champ arithmétique complet et les erreurs de régularité restent
  ouverts. L'équivalence moyenne/probabilité est prouvée pour tout déficit
  borné entre zéro et un, y compris sur des espaces variant avec l'échelle.
- **Polynôme signé : conserver les singletons.** L'expansion finie exacte vaut
  pour toute vraie loi plantée. Le coefficient à un site est sa moyenne plantée
  moins p ; il n'est pas supposé nul. À t=1, le numérateur est exactement la
  probabilité d'absence de départs restants. L'identification des coefficients
  avec les caractères affines et l'environnement conditionné reste à formaliser.
- **Borne selon les signes.** Pour une loi finie réelle, le déficit moyen est
  majoré par `(1-moyenne)_+ + sqrt(variance)/2`, et par un si R>=0. Le facteur
  un demi vient de l'égalité entre la partie négative centrée moyenne et la
  moitié de l'écart absolu moyen. Aucun petit-o séparé de ces deux termes n'est
  nécessaire. Le raccord de la variance à l'énergie de Walsh reste ouvert.

Aucune correction nouvelle des énoncés n'a été identifiée. Les points ci-dessus
précisent les étapes prouvées et leurs dépendances. Les bornes de noyaux, les
comptages CRT, l'activité des paires et les cumulants demeurent des travaux
mathématiques effectifs, non des tâches de simple documentation.

## Noyaux impairs rugueux — seizième lot

Les deux estimations finies précédant G.1 sont désormais établies sur les
entiers et leurs véritables noyaux `r_Y(m)`. Le paramètre de poids `z` est
indépendant du seuil `Y`. Pour la somme réciproque, le noyau égal à 1 est
retiré avant le produit eulérien, ce qui justifie exactement le terme « −1 ».
La somme utilise bien le nombre de facteurs premiers distincts du noyau.

**Simplification possible du papier, sans correction nécessaire.** Le facteur
`zeta(2s)` peut être omis dans ces deux bornes, pour `1/2 <= s < 1`.
La décomposition canonique `m=a²vr` donne au plus `floor(sqrt(X/(vr)))`
valeurs de `a`. Si `vr<=X`, ce nombre est au plus `(X/(vr))^s`; sinon
il est nul. La sommation sur les supports de `v` donne directement
`prod_{q<=Y}(1+q^(-s))`. Il n'est donc pas nécessaire d'élargir séparément
la somme sur `a` en une série zêta. Cette variante renforce la borne existante
et conserve sa précision asymptotique. Les fichiers du manuscrit ne sont pas
modifiés automatiquement.

**Seuil réel et domaine.** La définition formalisée utilise `floor(T)` pour
la borne entière; l'équivalence exacte avec `r_Y(m)>T` est prouvée pour
`T>=0`. La queue intégrale nécessite `Y>=1` et `s>0`; ces conditions sont
satisfaites dans le régime du papier. Le comptage traite aussi le seuil
entier nul et les intervalles vides.

**Portée obtenue.** Les suppressions supplémentaires sont comptées avec
multiplicité au plus `Q+1`, dans la population jusqu'à `n+Q`. La partition
entre suppressions initiales et supplémentaires est exacte. Le préfacteur
au seuil critique est borné par `exp(-V+epsilon*nu)`, uniformément pour
les populations agrandies `X>=M`, à partir du seul reste PNT déjà utilisé.
Le facteur explicite `1+T^sigma/sigma`, avec `sigma=1-s`, reste visible.

**Ce qui reste ouvert.** Il faut encore absorber ce facteur pour le `T_M`
littéral, terminer les limites et le couplage de suppression de G.1,
puis les allocations CRT et la régularité probabiliste des nuages.
Ce lot ne ferme donc pas G.1 ni les résultats suivants de l'annexe G.

## Seuil exact et suppressions renforcées — dix-septième lot

Le seuil `T_M=exp(theta H/u)` est traité littéralement, y compris son arrondi
pour comparer des noyaux entiers. Son élévation à la puissance `sigma=u/V`
donne exactement `exp(theta nu)`. La majoration élémentaire `1/sigma<=H`
suffit : avec `Q=O(H)`, tous les facteurs restants sont polynomiaux en H,
et leur logarithme est négligeable devant nu. Aucun développement plus fin
de `log(1/sigma)` n'est nécessaire. Les propriétés `T_M>exp(V)` à terme
(pour theta>0) et `log(T_M)/H -> 0` sont également prouvées.

**Simplification du comptage total.** Dès que `T>=1`, la condition
`r_Y(m)>T` implique que le plus grand premier de valuation impaire dépasse Y.
Ainsi G_theta est exactement l'intersection de la condition de profondeur
avec le bon ensemble défini par les seuls noyaux. Les anciens mauvais pivots
sont déjà exclus par cette dernière condition. On peut donc borner le
complément par la partie peu profonde et une seule population de petits
noyaux, sans additionner une seconde fois la suppression des mauvais pivots.
Il s'agit d'une simplification de preuve, pas d'une erreur du papier.

**Résultats obtenus aux paramètres du papier.** Pour tout epsilon>0, le
nombre de suppressions supplémentaires est au plus
`n*exp(-V+(theta+epsilon)*nu)`. Les contraintes auxiliaires de géométrie
sont déduites du régime du papier avec son E_* et son Y. Si theta<c,
la masse supplémentaire est au plus `exp(-(c-theta)*nu/2)` et tend vers zéro.
Le complément total vérifie `card(complement)*log(M)/M -> 0`.

**Remplacement conditionnel.** La loi de remplacement est construite comme
un mélange réellement normalisé avec un champ indépendant de Poisson sur
les coordonnées supprimées. Les coordonnées sont celles du champ signé sur
G0, et tous les types bas sont conservés à un site retenu. Les probabilités
marginales conditionnelles exactes donnent un coût d'au plus `2*p` par site
supprimé, pour tout événement positif du champ original des petits premiers.
Il n'apparaît aucun facteur `exp(I)` dans cette étape.

La dernière composition avec les suppressions initiales du champ complet
et les queues de marques reste à assembler en un énoncé commun ; G.1 garde
pour cette raison le statut partiel. Les allocations CRT et les probabilités
de régularité ne sont pas encore établies. Les fichiers du manuscrit restent
inchangés. Seules les estimations arithmétiques asymptotiques de ce lot
emploient le reste PNT déjà explicite dans la formalisation.

## Restauration complète et allocations CRT — dix-huitième lot

**G.1 terminé avec ses entrées arithmétiques explicites.** Les anciennes
suppressions, les queues de marques et le remplacement supplémentaire sont
réunis dans un énoncé sur le champ spatial infini, sous l'événement original
des petits premiers. Le coût supplémentaire est explicitement majoré par
`8*exp(-cprime*nu)+2*M^(-1/3+epsilon)+2*exp(-(c-theta)*nu/2)`.
Sa convergence vers zéro est prouvée pour theta<c, cprime>0 et epsilon<1/3.
Cette réduction n'emploie pas l'hypothèse de solution de Stein et ne suppose
pas que le champ remplacé est déjà proche de Poisson. Les entrées PNT,
Laishram–Shorey, Shorey et Nicolas–Robin restent celles des estimations
arithmétiques antérieures. La limitation séparée de F.2 reste inchangée.

**Précision utile pour la preuve de G.2 : les blocs vides.** Pour une
affectation des premiers du noyau aux blocs cibles, un bloc ne recevant
aucun premier a probabilité exactement un. Il faut donc multiplier par trois
seulement pour les blocs non vides. Leur nombre est au plus omega(r), ce
qui donne le facteur `3^omega(r)` annoncé ; utiliser `3^(k-1)` sans cette
précision ne donne pas la même borne. Lean traite uniformément ces deux
cas en majorant le coût d'un bloc par `3^(nombre de premiers affectés)/r_h`.
C'est une explicitation de la preuve du papier, pas un contre-exemple.

**Hypothèses à rappeler dans un énoncé autonome.** La borne CRT utilise
`r<=2n`, déduit ici de `r<=m<=2n`; le texte le déduit des échelles ambiantes.
L'unicité d'un hôte dans son propre support utilise `Y>Q`. Il serait utile
de rappeler ces deux conditions directement dans G.2 si le lemme doit se
lire indépendamment du début de l'annexe. Sans contrôle du produit par n,
le remplacement de `1/r_h+1/n` par `3/r_h` n'est pas justifié en général.

Le comptage complet des affectations est maintenant une véritable borne de
probabilité pour les indices uniformes indépendants, appliquée à tous les
premiers du noyau impair réel du modèle. La conversion
`z^omega(r)/r <= T^(-1+log(z)/log(Y))` est également prouvée. La définition
de régularité conserve chaque occurrence (bloc, position), y compris quand
deux occurrences ont la même valeur. Un support bon isolé est régulier ;
un défaut de régularité force tous les premiers d'une occurrence à être
hébergés dans les autres blocs.

Il reste à assembler la borne de probabilité sur toutes les occurrences
sources (facteur `k*(Q+1)`), puis à traiter le nombre poissonien de blocs
pour G.3. G.2 demeure donc partiel. Les fichiers du manuscrit sont inchangés.

## Borne globale de G.2 et nuage de taille poissonienne — dix-neuvième lot

**G.2 terminé.** On expose un indice source et on le retire du vecteur des
indices. Cette restriction est injective sur chaque fibre à indice fixé.
La borne CRT s'applique alors aux autres indices indépendants ; on moyenne
sur la valeur de l'indice source, puis on somme sur les `k*(Q+1)` occurrences.
La preuve est directement appliquée à la loi uniforme de la grille, avec le
seuil réel T et son arrondi exact pour le bon ensemble renforcé. Les conditions
ambiantes `Q<=n`, `Q<Y` et `3*k*(Q+1)<Y` restent explicites. Elles sont celles
utilisées dans la preuve du papier ; aucune nouvelle entrée bibliographique
n'est nécessaire.

**G.3 : moyenne avant troncature.** Le nuage spatial ordonné est construit
sur la réunion disjointe des espaces de k indices, avec masse égale à la masse
de Poisson en k multipliée par la vraie loi uniforme des k indices. Sa masse
totale vaut un. Les séries d'événements sont sommables avant leur regroupement.
Une perte `a*k+B` pour k<=K donne donc `a*Lambda+B` plus la queue de Poisson.
Cela garde le coût des sites exclus à `Lambda*card(complement)/n`, sans le
remplacer inutilement par `ceil(2*Lambda)*card(complement)/n`.

La série génératrice exacte et Markov en base deux donnent, sans constante
supplémentaire, `P(N>ceil(2*Lambda))<=exp(-(2*log(2)-1)*Lambda)`. Sa convergence
vers zéro conserve expressément `Lambda->infinity`, déjà imposé par le budget
microscopique au début de l'annexe F et repris dans G. Il n'y a donc pas ici
d'hypothèse manquante dans le papier ; ce point doit simplement rester visible
quand on cite la borne de queue séparément.

La borne finie pour le nuage spatial est maintenant
`Lambda*card(complement)/n + K*(Q+1)*T^(-1+log(3*K*(Q+1))/log(Y))
+ exp(-(2*log(2)-1)*Lambda)`, avec K=ceil(2*Lambda). Elle inclut les indices
répétés et toutes les occurrences brutes : la régularité impose toujours un
premier privé à chaque occurrence.

**Limite actuelle.** Le raccord de ce nuage ordonné au champ cible complet,
avec les signes et tous les excès, n'est pas encore enregistré. Les queues
de marques et l'absorption aux échelles exactes du papier restent aussi à
assembler pour obtenir la dernière borne et le o(1) de G.3. Cette dernière
reste donc partielle. Les sources du manuscrit ne sont pas modifiées.

## Cible marquée complète et absorption de G.3 — vingtième lot

**Raccord à la vraie cible.** La loi des rangées de Poisson géométriques déjà
utilisée dans le dépôt coïncide avec la somme d'un nombre poissonien de points,
chacun portant une position uniforme, un excès géométrique et un signe équitable
indépendants. L'identification vaut sur tout ensemble fini non vide de sites,
sans tronquer les excès. Les projections finies déterminent la loi complète ;
aucune hypothèse supplémentaire sur les queues n'est requise pour cette identité.
Les préfixes de positions et les masses de chaque paire (nombre, grille) donnent
exactement la loi ordonnée utilisée dans la preuve CRT du lot précédent.

**Clarification utile pour le papier.** Définir la régularité comme une propriété
d'une configuration admettant une énumération finie rend explicite son passage
entre le nuage ordonné et la mesure ponctuelle. La masse totale est celle de
la configuration, avec ses multiplicités, et chaque occurrence brute doit avoir
son premier privé. Le vide satisfait la définition. Les répétitions ne peuvent
pas être perdues lors de ce passage : elles sont conservées dans la somme des
masses de Dirac et dans les occurrences des supports. La borne établie porte
sur la cible complète, et ne fournit toujours pas un contrôle de masse exacte
ou d'absence d'occurrences supplémentaires pour le champ arithmétique.

**Arrondis exacts.** Pour exp(V)>=2, `V-log 2 <= log(floor(exp V)) <= V`.
Pour Lambda>=1, `ceil(2*Lambda)<=3*Lambda`. Le coût logarithmique restant est
au plus `log(18*B)+log H` lorsque Q+1<=B*H ; il est o(nu). Cela justifie le
facteur 1/2 dans la marge CRT du papier sans remplacer les arrondis par des
équivalents non quantifiés.

L'identité exacte
`nu^2/(u*V)=(exp(u)/u^3)/(1-Ei(u)/exp(u))`
au saddle dur prouve sa divergence. Elle absorbe uniformément tout facteur
dont le logarithme est <=V+C*log H, et en particulier K*(Q+1), dans
`exp(-c*theta*nu^2/(4*u))`. Ce dernier terme tend vers zéro pour c,theta>0.
Il n'y a pas de correction mathématique du manuscrit identifiée ici ; ces
calculs peuvent simplement détailler les deux phrases d'absorption de G.3.

La borne complète obtenue aux paramètres exacts du papier est
`Lambda*card(indices exclus)/(M-L) + exp(-c*theta*nu^2/(4*u))
+ exp(-(2*log 2-1)*Lambda) + Lambda/2^(E_*+1)`.
Toutes les conditions géométriques et CRT proviennent de la bande de longueurs
et du budget d'information, après un seuil uniforme. Cette étape probabiliste
n'utilise pas d'entrée analytique ou arithmétique bibliographique.

**Reste de G.3.** Il faut encore composer les estimations des indices exclus
et de la queue des marques avec ce résultat, puis utiliser Lambda->infinity
pour enregistrer la borne asymptotique complète et son o(1). Les identités
de présence sont déjà établies ; les étapes ultérieures G.4/G.5 et les
compléments de Fourier/cumulants restent ouverts. Les sources du papier
sont conservées à l'identique.

## Masses et vides de Palm arithmétiques — vingt-et-unième point de validation

**G.3 terminé.** La borne complète rassemble les cinq termes affichés et leur
convergence aux paramètres du papier. Pour le comptage des indices exclus,
le terme o(nu) est formalisé par une marge arbitraire eta>0. Avec theta<c,
prendre eta=(c-theta)/2 suffit. La queue poissonienne requiert bien
Lambda->infinity ; cette hypothèse est conservée explicitement.

**Passage présence / masse exacte.** Sur une configuration régulière, les sites
sont distincts. Le calcul de la masse de la cible complète (signes et excès non
tronqués) donne exp(-mu) fois le même produit que la présence arithmétique. La
source est la mesure infinie originale, conditionnée par l'événement réel sur
les petits premiers. Aucune hypothèse de factorisation des masses exactes
n'est ajoutée : la masse exacte est la présence multipliée par le vrai vide de Palm.

**Précision utile dans la preuve de G.4.** L'équivalence entre « aucun atome
supplémentaire » et « aucun départ supplémentaire » est presque sûre. Un départ
pourrait, sur une réalisation exceptionnelle, être suivi d'une plage infinie et
ne produire aucune marque exacte finie. Le théorème de terminaison simultanée
des plages exclut cet événement. L'absolue continuité des deux conditionnements
préserve cette propriété. Il serait utile d'ajouter « presque sûrement, par
finitude des plages » à la phrase correspondante de la preuve.

**Normalisation et simplification de G.5.** L'erreur logarithmique est bornée
par K*p+g*p^2/(1-p), version légèrement moins fine mais suffisante du papier.
Avec K=ceil(2*Lambda), g<=n et Lambda>=1, elle est <=5*Lambda*p. Le budget
la rend <=M^(-1/2) uniformément. Pour déduire seulement la disparition du
déficit unilatéral, l'inégalité « moyenne normalisée <= TV + erreur de
normalisation » suffit : il n'est pas nécessaire de faire intervenir la masse
des configurations irrégulières. Celle-ci reste requise pour l'approximation
bilatérale de G.4. Le raccord exact de l'ensemble régulier nommé dans G.3,
après changement de coordonnées et restriction, doit encore être enregistré.

**Convention à expliciter pour le logarithme du vide.** Dans la phrase qui
définit L_z=(-log v(z)-Lambda)_+, il faut entendre L_z=+infinity si v(z)=0,
puis exp(-infinity)=0. Le logarithme réel totalisé de Lean vérifie log(0)=0 ;
il ne peut pas être utilisé directement pour cette phrase. La preuve du
déficit borné évite complètement cette convention. Le passage sur l'intégrale
impropre plus loin dans G précise déjà +infinity ; harmoniser les deux passages.

**Signes et environnement.** L'inversion de Walsh et l'identité de Parseval
sont établies pour les coefficients calculés sur la vraie loi uniforme des
signes. La moyenne du caractère d'une fibre affine conserve exactement sa
phase. Un plant de plein rang préserve toute la loi d'environnement, y compris
après conditionnement. Sa transformée de Fourier reste donc dans la formule,
et ne se remplace par un indicateur de fréquence nulle que sous la loi uniforme
non conditionnée. L'assemblage des moments centrés et l'instanciation complète
avec les matrices arithmétiques de G.6 restent à finir.

Les fichiers livrés par l'auteur restent inchangés ; ces points sont des
suggestions pour une révision ultérieure du texte, pas des modifications tacites.

## Raccords de Palm, cumulants finis et témoin arithmétique — vingt-deuxième point

**G.4 : coordonnées et suppression.** Le passage j -> j+1 est désormais exact
pour la cible marquée complète, avec ses multiplicités. La restriction de
l'ensemble régulier de G.3 donne bien l'exception nommée dans G.4. La suppression
relie les véritables vides de Palm du champ complet et du champ retenu, avec le
coût ordinaire de départs extérieurs. La pénalité peut être donnée explicitement
par 5*Lambda^2/n. Le raccord asymptotique séparé des coûts extérieurs reste à
consigner dans la revue des assertions non numérotées.

**G.6 : matrices effectives.** Les coefficients centrés portent sur les matrices
de valuations et les vrais indicateurs arithmétiques. La régularité construit les
pivots et prouve le plein rang du plant. Les termes singletons, les recouvrements
et la transformée de Fourier de l'environnement conditionné restent présents.
L'inégalité de Walsh est appliquée au véritable polynôme normalisé non négatif.

**Simplification possible de la preuve de G.8.** Après l'expansion en partitions,
on peut majorer la somme des collections disjointes de blocs par le produit fini
prod_B(1+w_B), puis utiliser 1+w_B<=exp(w_B). Avec w_B=2*b_B, cela donne la
constante (exp(2*K)-1)/2, sans passer par une somme indexée par le nombre de blocs
et ses factorielles. La même preuve donne l'enveloppe polynomiale. Pour F_2,
on peut développer directement les indicatrices de catégories et utiliser la
même famille de sous-ensembles à sites distincts ; aucune contribution interne
à un même site n'est ajoutée. C'est une simplification facultative du texte.

**Convention de cumulants.** La définition formelle est récursive et finie.
Pour les ordres >=2 de G.8, elle est appliquée à la table des moments centrés ;
les singletons s'annulent. La revue finale devra garder explicite cette
convention lorsqu'elle traitera les cumulants de Palm, dont les singletons
centrés au paramètre de référence p ne s'annulent pas nécessairement.

**G.7 : deux rangs réellement différents.** La formule de déviation absolue est
prouvée avec les nullités complète et au-dessus du seuil distinctes. Une moyenne
conditionnelle n'est donc pas remplacée par la seule covariance non conditionnée.
Le comptage CRT avec un seul bloc cible donne une constante deux extérieure,
pas une perte par facteur premier. L'assemblage de l'activité reste ouvert.

**G.9 : témoin dans la loi d'origine.** La réalisation où seul le premier q est
négatif produit réellement la marque (0,+) aux frontières tq certifiées. Le
comptage exact, sa survie à des suppressions arbitraires et la probabilité
2^(-pi(C)) sont démontrés. On obtient une borne logarithmique finie sur
l'activité du champ arithmétique lui-même. Les limites le long de la sous-suite
de premiers, puis la divergence des ordres >=3, restent à assembler.

Les 28 fichiers du manuscrit livrés par l'auteur ne sont pas modifiés.

## Obstruction le long des premiers — vingt-troisième point

**G.9 : simplification des logarithmes.** Pour 0<=r<=1/4, on a directement
log(1-2r)>=-4r et log((3-2r)/(1-2r))>=log 3. On peut donc remplacer le
développement log 3+O(r) par une minoration exacte, dans le sens utile à la
preuve. La borne finie sur l'activité est
(N_ret*log 3-pi(C)*log 2-4*g*r)/2. C'est une simplification facultative,
qui conserve la constante finale du papier.

**Arrondis et cylindre.** Le comptage peut être minoré uniformément par
M/q-3-2*M/q^2 avant les suppressions. La preuve formelle utilise exactement
M=2^(q-1+floor(log_2 q)), le cutoff E_* du papier et C=M+Q. Ce dernier point
compte : remplacer C par un cylindre commode de taille environ 2M doublerait
inutilement le coût entropique du témoin et ferait perdre la constante annoncée.
Le cylindre M+Q suffit aux vraies coordonnées, et Q=o(M) est démontré.

**Bords de l'ensemble retenu.** G0 et G_theta sont contenus dans [1,M-L].
La quantité d'omissions du témoin est comptée dans [1,M] : elle comporte aussi
les L sites terminaux. L'identité exacte entre ces deux nombres de suppressions
est désormais prouvée ; leur coût normalisé tend bien vers zéro.

**Portée désormais raccordée.** La constante log(2)*(log(3)-1)/2 est strictement
positive et minore la limite inférieure normalisée pour G0 et tout G_theta fixe.
Les moyennes exactes sont déduites des pivots privés, et la seule hypothèse
arithmétique de cette minoration est le PNT déjà déclaré. La divergence de
l'activité totale suit sur toute suite de premiers tendant vers l'infini.
La convergence microscopique indépendante est spécialisée aux mêmes fenêtres,
avec les hypothèses analytiques et arithmétiques existantes de F.2. Le passage
à la divergence des seuls ordres >=3 reste suspendu à l'estimation de paires G.7,
et non à une nouvelle hypothèse d'obstruction.

**Cumulants de Palm.** L'inégalité non numérotée |R-1|<=exp(A)-1 est maintenant
prouvée par la même majoration finie en produits. Le terme singleton est
exactement E_Palm[J]-p ; aucune égalité de cette moyenne avec p n'est supposée.
La convention entre cumulants centrés d'ordre supérieur et cumulants bruts
reste à expliciter dans la revue finale.

Les 28 fichiers du manuscrit livrés par l'auteur restent inchangés.

## Paires absolues et divergence supérieure — vingt-quatrième point

**G.7 : simplification facultative de la preuve finale.** Une paire régulière
au sens des pivots privés a exactement sa loi produit, même après un événement
sur les petits premiers : sa covariance conditionnelle est donc nulle. Pour
les autres paires, la majoration positive du joint donne directement
`|Cov_A| <= rate_i*rate_k*(2^rho_full+1)/P(A)`. Elle se décompose en l'excès
`2^rho_full-1` et deux unités réservées aux paires non régulières. Toute paire
non régulière de bons supports force un hébergement de noyau impair rugueux
dans l'autre support. Le comptage CRT à une cible puis le point selle donnent
la même borne `M^2 exp(-2V+o(nu))`. Cette voie évite d'utiliser la formule à
deux rangs dans l'assemblage final de G.7 ; cette formule reste formalisée
séparément et garde son intérêt explicatif. Aucun changement d'énoncé requis.

**Conditionnement.** La borne conserve un seul facteur `1/P(A)` et, après
usage du budget, le gain supplémentaire `exp(-I)` : pour tout `0<d<2c`,
l'activité des paires est au plus `4 exp(-I-d*nu)+2 M^(-1/3+epsilon)`.
Les catégories de signes et d'excès sont sommées avant les coûts géométriques.
Il n'apparaît donc aucun facteur artificiel égal au nombre de catégories.

**G.9 : facteur deux et ordres supérieurs.** Le double comptage des ensembles
transversaux de cardinal deux identifie exactement la convention de l'activité
cumulante avec la somme des covariances sur les paires ordonnées. Le facteur
deux de l'énoncé est ainsi vérifié. Avec la disparition de cette couche et la
divergence totale déjà obtenue, la divergence des ordres au moins trois est
maintenant prouvée pour G0 et chaque G_theta fixé. La comparaison microscopique
reste indépendante de ce calcul d'activité, avec les entrées analytiques de F.2.
