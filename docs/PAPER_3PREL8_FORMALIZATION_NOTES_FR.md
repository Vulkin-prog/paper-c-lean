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
