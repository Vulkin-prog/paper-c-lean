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
