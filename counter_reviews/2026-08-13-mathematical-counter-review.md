> **Provenance.** Report supplied by the repository owner on 2026-08-13.
> The supplied text does not encode the author/model or the exact prompt. It is
> therefore recorded as an agent-generated counter-review, not independent
> human peer review. Original SHA-256:
> `eb019bb4598c559aef04ad1efd93dce361894ed4c57938623b976db0fe1b3d4c`.
> Scope: Paper C v08/v09 mathematical architecture and manuscript junctions.

# Rapport de contre-review mathématique

J’ai examiné l’ensemble du manuscrit, en suivant en priorité les points où une erreur locale ferait tomber toute l’architecture : formulation affine, estimation des défauts, décomposition rationnelle/résiduelle, fermeture des noyaux profonds, argument de conditionnement–Chen–Stein, processus marqués et recollement global.

## Verdict général

**Je ne trouve pas de contre-exemple ni de contradiction fatale dans le théorème principal dyadique.** Le cœur mathématique du papier est plausible, remarquablement cohérent compte tenu de sa longueur, et plusieurs passages que l’on pourrait spontanément soupçonner résistent à un contrôle détaillé.

Je ne recommanderais toutefois **pas l’acceptation dans l’état actuel**. Ma recommandation serait :

> **révision majeure, ou rejet avec invitation explicite à resoumettre.**

La raison n’est pas une formule manifestement fausse. Elle tient à la combinaison de trois problèmes :

1. la partie la plus fragile — l’extension à rapport borné et le recollement global — est en grande partie présentée comme un transport de dizaines d’estimations antérieures ;
2. la formalisation Lean, qui pourrait précisément lever cette difficulté d’audit, n’est pas reproductible à partir des éléments transmis ;
3. quelques jonctions sont laissées implicites, et les affirmations sur la portée exacte de la vérification formelle sont plus fortes que ce qui est réellement mécanisé.

Mon niveau de confiance par résultat serait le suivant.

| RésultatAppréciation                                 |                                                                                   |
| ---------------------------------------------------- | --------------------------------------------------------------------------------- |
| Théorème 1.4, moments et somme homogène dyadique     | **Crédible et techniquement solide**                                              |
| Théorème 1.1, Poisson en variation totale            | **Crédible**, sous réserve de la somme homogène                                   |
| Théorème 1.2(i), masques déterministes               | **Crédible**                                                                      |
| Théorème 1.2(ii), processus spatial                  | **Crédible**                                                                      |
| Théorème 1.2(iii), processus marqué                  | **Crédible après explicitation d’une jonction locale**                            |
| Théorème 16.2 et Corollaire 16.4, recollement global | **Plausibles, mais les moins auditables du papier**                               |
| « Vérifié en Lean »                                  | **Non utilisable comme preuve indépendante sans l’archive et un build reproduit** |

---

# 1. Ce qui tient bien mathématiquement

## 1.1 La formulation affine est correcte

Le passage de la fonction multiplicative aux vecteurs de parités

[
v(n)=(v\_p(n)\bmod 2)\_p
]

est exact. L’événement (J\_{x,L}) correspond bien à (L) équations affines sur (\mathbf F\_2), et l’identité de Fourier du Lemme 2.1 donne correctement

[
\mathbb P(J\_{x\_1,L}=\cdots=J\_{x\_k,L}=1)
\=2^{-kL}\eta(\mathbf x)2^{\rho(\mathbf x)}.
]

Le point important est que l’incompatibilité affine ne produit pas une probabilité négative ou un terme oscillant incontrôlé : elle est absorbée par (\eta\in{0,1}), puis par

[
|\eta 2^\rho-1|\le 2^\rho-1.
]

La traduction des relations homogènes en sous-ensembles pairs de sommets dont le produit est un carré est également correcte. Sur un arbre, le passage « sous-ensemble d’arêtes (\leftrightarrow) bord pair de sommets » est bijectif.

## 1.2 L’argument Runge–code de Hamming est convaincant

Le Lemme 3.1 est l’un des endroits les plus risqués du manuscrit, car le degré (d) croît avec (N). J’ai contrôlé les deux branches de la preuve :

- troncature de l’expansion de
  [
  \prod\_{\nu=1}^d(1+\gamma\_\nu z)^{1/2};
  ]
- cas exceptionnel où l’approximation polynomiale coïncide exactement avec la racine carrée.

Le dénominateur uniforme (2^d), la borne de Cauchy sur la queue et la borne de hauteur du polynôme entier (Q) sont compatibles avec un degré variable. Je ne vois pas ici de constante secrètement choisie pour un degré fixé.

Dans la Proposition 3.2, l’ajout de la dernière coordonnée égale à (1) force les mots du code à avoir un poids pair. Un mot non nul fournit donc bien un produit d’un nombre pair d’entiers distincts qui est un carré, auquel le lemme de Runge s’applique. Le choix de

[
t\_0=\left\lfloor \frac12\left(c\frac{\log N}{\log H}-1\right)\right\rfloor
]

évite correctement la faute classique consistant à déduire une majoration de (t\_0) d’une simple minoration de la distance minimale.

La somme pondérée

[
\sum\_u (2^{m\_u}-1)\le N^{1/2+o(1)}
]

est ensuite cohérente : il y a (N^{1/2+o(1)}) entiers dont la partie sans carré est (H)-friable, et chaque fenêtre n’en contient que (O(\log N/\log\log N)).

## 1.3 La décomposition rationnelle/résiduelle est bien conçue

Les « unités exactes »

[
a(x+i)=b(y+j)
]

engendrent effectivement un sous-espace de relations de dimension (m-1), formé des sous-ensembles pairs des (m) unités. La borne (a,b\le L) dès qu’il y a deux unités est correcte, car deux solutions diffèrent de ((b,a)).

La séparation entre

[
\rho=\sigma+\tau
]

est utilisée proprement :

- (\sigma) mesure le code rationnel systématique ;
- (\tau) mesure le quotient résiduel après contraction.

La précaution concernant les canaux ayant zéro ou une seule unité est importante et, contrairement à beaucoup de textes de ce type, elle est effectivement respectée plus loin. L’exemple explicite de la page 15 montre que l’auteur a identifié une vraie possibilité de faute : avec une seule unité, on ne peut pas déduire (a,b\<B) ni l’identité des valuations au-dessus de (B).

## 1.4 Le graphe des grands premiers et le quotient dimensionnel sont corrects

Pour (p>B), une fenêtre de diamètre (B-1) contient au plus un entier ayant une valuation impaire en (p). Les équations correspondantes sont donc bien de trois types :

- variable fixée à zéro ;
- égalité de deux variables, une dans chaque bloc ;
- aucune équation.

Cela donne correctement

[
\dim W\_{>B}=D+c,\qquad D+2c\le 2B.
]

Le passage au quotient par le code rationnel utilise une parité de bloc supplémentaire. La formule

[
\tau\le D^#+c^#
]

est cohérente : après avoir retranché (m-1) dimensions du code rationnel, la parité du premier bloc enlève encore une dimension.

## 1.5 Les secteurs modérés sont correctement fermés

Les estimations CRT des Sections 7.1–7.3 résistent au contrôle des facteurs combinatoires :

- les certificats sont non ordonnés, d’où le (1/r!) ;
- les premiers sont distincts ;
- chaque premier impose une ou deux classes de congruence selon la présence ou non d’un canal rationnel ;
- le produit (P^#\le N) permet de remplacer « longueur de l’intervalle divisée par (P), plus un » par (O(N/P)).

Les exposants annoncés sont cohérents. En particulier, au seuil

[
c^#\le \alpha B,\qquad \alpha=\frac{3}{16},
]

on obtient bien

[
4^{c^#}=2^{2c^#}
\le 2^{3B/8}
\=N^{3/8+o(1)},
]

puis, après Cauchy–Schwarz avec (N^{3/2+o(1)}) hôtes,

[
R\_{\rm res}\le N^{31/16+o(1)}=o(N^2).
]

## 1.6 L’exclusion des cœurs alignés est plausible et bien fermée

Dans le Théorème 8.1, l’argument de codage extrait un petit nombre de composantes résiduelles dont l’union donne un produit carré. Les deux coordonnées supplémentaires du code garantissent que le nombre de sommets choisi dans chaque bloc est pair. C’est essentiel pour que

[
G(ax)=a^{|I|}b^{|J|}
\prod\_{i\in I}(x+i)\prod\_{j\in J}(y+j)
]

soit lui-même un carré entier.

La non-collision des racines de (G) est obtenue en retirant les composantes contenant des unités exactes. La borne de Runge donne alors

[
\log N\ll d\log(dB^{A+1})
\=O\_\alpha!\left(\frac{B}{\log\log B}\right)
\=o(B),
]

en contradiction avec (\log N=(\log 2)B+O(1)).

Je ne vois pas d’unité exacte oubliée dans les trois cas (m=0), (m=1) et (m\ge2).

## 1.7 La fermeture terminale par déterminants et Pell est le passage le plus convaincant

Dans une composante isolée de deux sommets, les noyaux complets

[
R\_t=K\_B(x+i\_t)=K\_B(y+j\_t)>1
]

sont deux à deux premiers entre eux. Pour deux composantes,

[
R\_sR\_t\mid
(x+i\_s)(y+j\_t)-(x+i\_t)(y+j\_s).
]

La non-annulation du déterminant est correcte : une annulation produirait deux unités d’un canal rationnel de hauteur au plus (L), contredisant le caractère non aligné.

Il s’ensuit qu’au plus un noyau dépasse ((CNB)^{1/2}). Le comptage des entiers dont le noyau est sous ce seuil donne

[
N^{3/4+o(1)}
]

premiers starts possibles. Pour un start fixé, deux composantes isolées donnent une équation de Pell généralisée

[
Ra z^2-Sb w^2=j-v,
]

avec (Ra/Sb) non carré. Le nombre de partenaires est (N^{o(1)}). La masse terminale est donc

[
N^{3/4+o(1)}\cdot N^{1+o(1)}
\=N^{7/4+o(1)}.
]

Cet enchaînement paraît correct.

## 1.8 La partie probabiliste est propre

Le choix

[
Y=\lfloor B^2\log B\rfloor
]

réalise correctement le compromis suivant :

- assez petit pour que les entiers (Y)-défectueux aient une masse (N^{1/2+o(1)}) ;
- assez grand pour que le nombre de paires de fenêtres partageant un premier (p>Y) soit
  [
  O!\left(\frac{N^2}{\log^2 B}\right).
  ]

Pour un bon start, les (L) lignes ont des pivots privés parmi les coordonnées (p>Y). La marginale conditionnelle est donc exactement (2^{-L}), indépendamment de la réalisation des petits premiers.

Le graphe obtenu est un vrai graphe de dépendance conditionnel : hors du voisinage, les événements dépendent de familles disjointes de coordonnées premières.

La décomposition des paires en

- chevauchement strict : probabilité conjointe nulle ;
- contact à distance (L) : rang conditionnel (2L) ;
- séparation stricte : contrôle par (2^{\rho(x,y)}),

est correcte.

Le taux

[
d\_{\rm TV}\ll\_C(\log\log N)^{-2}
]

vient bien du terme

[
2^{-2L}E\_Y\asymp \frac1{\log^2 B},
]

et non de la partie diophantienne, qui laisse une marge exponentielle.

---

# 2. Contrôle des résultats externes essentiels

J’ai vérifié plusieurs des transcriptions bibliographiques les plus sensibles.

## 2.1 Evertse–Silverman

La spécialisation utilisée au Lemme 9.1 est compatible avec le Théorème 1(b) d’Evertse–Silverman : pour un polynôme ayant au moins trois racines dans le corps (L), le nombre de valeurs entières pertinentes est exponentiel en la taille de (S) et dans le rang 2-torsion du groupe de classes. Pour (K=L=\mathbf Q), le groupe de classes est trivial, et la dépendance restante est bien exponentielle en

[
1+\omega(e)+
\omega!\left(\prod\_{r\<s}(h\_r-h\_s)\right).
]

Le facteur supplémentaire (2) pour les deux signes de (Y) est légitime. ([ir.cwi.nl](https://ir.cwi.nl/pub/1788/1788D.pdf "https://ir.cwi.nl/pub/1788/1788D.pdf"))

## 2.2 Laishram–Shorey

La borne utilisée au Lemme 15.2 découle bien du Corollaire 1 de Laishram–Shorey :

[
\omega(\Delta)\ge
\min!\left(
\pi(k)+\Big\lfloor\frac34\pi(k)\Big\rfloor-1+\delta(k),
\pi(2k)-1
\right).
]

Le manuscrit abandonne le terme non négatif (\delta(k)), ce qui est sans danger. En revanche, la phrase selon laquelle le premier terme vaudrait « sauf pour une liste finie explicite » n’est pas une présentation fidèle du corollaire final, qui est déjà formulé sans exception. C’est une imprécision bibliographique, pas une faute dans la minoration utilisée. ([impan.pl](https://www.impan.pl/shop/en/publication/transaction/download/product/83314 "https://www.impan.pl/shop/en/publication/transaction/download/product/83314"))

## 2.3 Balasubramanian–Shorey

Le Théorème 1 de la source primaire a bien la forme requise : pour (k\ge27), l’équation

[
(m+d\_1)\cdots(m+d\_t)=by^2,
\qquad P^+(b)\le k,
]

avec (m>k^2) et (t\ge\mu\_k(\theta\_0)), force (k) à être borné. Le produit des sommets défectueux de la fenêtre fournit exactement une équation de cette forme. La notice bibliographique correspond bien à l’article invoqué. ([impan.pl](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/65/3 "https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/65/3"))

Je n’ai donc identifié aucune mauvaise spécialisation manifeste parmi ces trois ponts externes.

---

# 3. Objections majeures

## 3.1 La vérification Lean ne peut actuellement pas servir de garantie indépendante

Le manuscrit affirme que les Sections 2 à 17 ont été formalisées dans un développement de 146 000 lignes et 4 070 déclarations publiques. Il précise cependant lui-même que les sept résultats bibliographiques sont importés comme hypothèses, et sont donc invisibles à `#print axioms`. Il indique aussi que le DOI est seulement « reserved before deposit ». Dans les éléments qui m’ont été transmis, seul le PDF est présent : ni l’arborescence `paper_c_lean/`, ni le manifeste, ni les fichiers de build, ni le commit revendiqué ne sont disponibles.

C’est une objection sérieuse pour trois raisons.

### a. `#print axioms` ne valide pas les sept transcriptions

Une proposition fausse passée comme paramètre explicite à un théorème Lean ne figure pas parmi ses axiomes. Il faut donc vérifier séparément :

1. que chaque transcription correspond exactement au théorème publié ;
2. que les quantificateurs et uniformités sont corrects ;
3. que les théorèmes finaux conservent effectivement ces hypothèses dans leur signature.

Le registre de fingerprints annoncé est précisément l’objet qui permettrait cet audit, mais il n’est pas accessible ici.

### b. Certaines affirmations ne sont pas formalisées littéralement

Le papier indique que la convergence des processus ponctuels est mécanisée seulement sous forme de convergence des fonctionnelles de Laplace. L’équivalence avec la convergence vague vers un processus de Poisson est laissée à la théorie générale non formalisée.

De même, le conditionnement de la Section 13 est représenté par une loi uniforme sur un cylindre fini, sans théorie mesure-théorique de l’espérance conditionnelle.

Ces remplacements sont mathématiquement raisonnables. Ils signifient toutefois que la phrase « les énoncés et preuves ont été formalisés dans leur intégralité » doit être remplacée par une description plus exacte :

> les noyaux combinatoires et probabilistes finis ont été formalisés, et certains passages vers les formulations probabilistes usuelles reposent encore sur des théorèmes externes non mécanisés.

### c. Le build doit être rejoué par un tiers

Avant publication, le dossier devrait contenir un dépôt immuable permettant réellement de lancer :

```
lake build
[audit des hypothèses et des fingerprints]

```

avec les versions exactes de Lean et Mathlib.

**Conséquence de referee :** dans l’état, je n’accorderais aucun poids probatoire supplémentaire à l’affirmation Lean. Le texte mathématique doit être jugé comme une preuve conventionnelle de 70 pages.

## 3.2 L’Appendice 17 est la partie la moins auditée du papier

Le Théorème 16.2 repose sur la Proposition 16.1, qui transporte la somme homogène de ([N,2N)) à ([N,\kappa N)) pour (\kappa) borné.

Le texte identifie correctement un changement non trivial : le canal (2:1), négligeable dans un bloc dyadique, devient volumique et fait passer les masses systématiques de

[
N^{4/3+o(1)},\quad N^{5/3+o(1)}
]

à

[
N^{3/2+o(1)},\quad N^{2+o(1)}.
]

Cela montre justement que le passage à rapport borné n’est pas une simple modification cosmétique.

L’Appendice 17 énumère de nombreux lemmes de stabilité, mais leurs preuves sont souvent réduites à « la preuve antérieure s’applique après R1–R10 ». Je n’ai trouvé aucune incohérence précise dans ces transports, mais cette présentation laisse une charge d’audit disproportionnée au referee :

- les (o\_{C,\kappa\_0}(1)) doivent être uniformes à chaque étape ;
- les constantes du comptage CRT, des déterminants, de Pell et des hôtes terminaux doivent être fixées dans le bon ordre ;
- les changements (N\mapsto c\_{\kappa\_0}N) doivent être propagés dans tous les résultats diophantiens ;
- le canal (2:1) modifie une borne quadratique utilisée plus loin dans les secteurs modérés.

La formalisation accessible pourrait suffire à lever cette objection. Sans elle, je demanderais soit une preuve beaucoup plus développée de la Proposition 16.1, soit une annexe autonome donnant pour chaque secteur l’énoncé exact transporté et les constantes consommées.

## 3.3 La forme quantitative de la somme homogène est moins transparente que la forme qualitative

La Proposition 11.2,

[
R\_2(N,L)=o\_C(N^2),
]

est correctement assemblée à partir des sept secteurs.

Le Corollaire 11.3 affirme plus précisément

[
R\_2(N,L)\ll\_C
N^2\exp!\left(
-c\_R\frac{\sqrt{\log N}}{\log\log N}
\right).
]

Cette forme dépend du choix d’un (C\_{\rm term}) extrait d’une estimation en notation (O), puis d’un (K) tel que

[
K>\frac{2C\_{\rm term}}{\log 2}.
]

Ce n’est pas logiquement incorrect : une constante implicite peut être fixée, puis majorée. Mais la chaîne n’est pas assez explicite pour qu’un lecteur puisse vérifier la prétention quantitative sans reconstruire plusieurs couches de constantes.

Je recommanderais d’isoler un lemme de la forme :

> Il existe des constantes explicitement fixées (C\_{\rm host}) et (N\_0) telles que, pour tout (N\ge N\_0), le nombre d’hôtes terminaux satisfait…

puis de déduire le choix de (K) dans un corollaire séparé.

Cette objection concerne surtout le **taux exponentiel**, pas le (o(N^2)) qualitatif.

---

# 4. Jonctions locales à expliciter

## 4.1 Processus marqué : paires proches mais à supports disjoints

Dans la Section 14.4, pour (x\<y), le texte pose

[
r\_e=L+e,\qquad d=y-x
]

et traite explicitement :

- (d\<r\_e) : incompatibilité ;
- (d=r\_e) : une composante avec un cycle ;
- (d=r\_e+1) : arbres se touchant en un sommet ;
- (d>r\_e+1) : supports disjoints.

Il passe ensuite directement aux paires avec (|x-y|>Q), où

[
Q=L+E+1.
]

Il reste donc textuellement le régime

[
r\_e+1\<d\le Q.
]

Il n’y a pas de véritable obstruction mathématique. Dans ce régime, les supports sont disjoints et leur union est contenue dans un intervalle de diamètre au plus (2Q). Or

[
Y\_Q=(Q+1)^2\log(Q+1)>2Q
]

pour (Q) grand. Un premier (p>Y\_Q) ne peut donc diviser deux entiers distincts de cette union. Les deux supports ne peuvent partager aucune coordonnée première (p>Y\_Q), et ces paires ne sont simplement **pas des arêtes du graphe conditionnel**.

Une phrase explicitant ce fait ferme complètement la jonction. Dans la version actuelle, c’est une lacune de rédaction plutôt qu’une faille du résultat.

## 4.2 Proposition 9.11 : domaine implicite (D^#\le2)

Juste avant la Proposition 9.11, la Proposition 9.9 élimine les paires ayant (D^#\ge3), puis le texte annonce « We may now assume (D^#\le2) ».

La Proposition 9.11 affirme ensuite que toute la masse du cœur profond non aligné hors de (T\_K) est (o(N^2)), alors que sa preuve travaille essentiellement sous (D^#\le2).

L’énoncé est vrai en combinant les Propositions 9.9 et 9.11, mais il devrait être formulé de l’une des deux manières suivantes :

- restreindre explicitement la Proposition 9.11 à (D^#\le2) ;
- ou commencer la preuve par « le secteur (D^#\ge3) est traité par la Proposition 9.9 ».

## 4.3 « Plage maximale » devrait être définie plus précisément

L’événement (J\_{x,L}) fixe le bord gauche, mais ne fixe pas le bord droit :

[
f(x-1)=-f(x),\qquad
f(x)=\cdots=f(x+L-1).
]

Il signifie donc directement :

> une plage constante de longueur au moins (L), dont le bord gauche est (x).

Ce n’est qu’après avoir prouvé que les plages infinies ont probabilité nulle que l’on peut parler sans réserve de la plage maximale commençant en (x).

La mathématique est correcte, mais la première définition devrait dire « start of a left-maximal stretch of length at least (L) » ou préciser immédiatement que le bord droit maximal est presque sûrement fini.

---

# 5. Revue section par section

## Sections 2–3 — Acceptables

La linéarisation, les relations comme parties paires, Runge, le code de Hamming, la masse des défauts et le premier moment me paraissent corrects.

Le Lemme 3.4 sur les paires qui se chevauchent ou se touchent est également correct : à distance (L), l’union des deux arbres est encore un arbre à (2L) arêtes.

## Sections 4–7 — Acceptables, mais très denses

Le comptage des hôtes relationnels

[
H\_2(N,L)\le N^{3/2+o(1)}
]

est cohérent. La première occurrence choisie dans une relation fournit bien, pour chaque premier de son noyau, une congruence dans l’autre bloc.

Le comptage des canaux rationnels et les sommes systématiques ont les bons exposants. Le traitement séparé du canal (2:1) dans un bloc dyadique est nécessaire et correctement fait.

Les certificats CRT et les secteurs à petit dénominateur sont convaincants.

## Section 8 — Acceptable

L’exclusion des cœurs alignés de densité linéaire est l’un des résultats les plus originaux du papier. L’argument code–Runge paraît fermé.

Je demanderais seulement que la constante (C\_\alpha) et le passage

[
\log\binom mt
\ge (C\_\alpha+o\_\alpha(1))\frac B{\log B}
]

soient présentés avec une ligne de calcul supplémentaire.

## Sections 9–10 — Acceptables sous les théorèmes externes

Les normalisations en équations hyperelliptiques ou de Pell sont correctes.

Le Lemme 9.5, qui compte simultanément les coefficients friables dans le cas de deux singletons, est essentiel : une sommation naïve sur les (2^{\pi(B)}) coefficients serait trop coûteuse pour obtenir le terme terminal exponentiel fin. La paramétrisation

[
X=ecu^2,\qquad
Y=(d/e)cv^2
]

est bien unique premier par premier.

La fermeture terminale est convaincante.

## Sections 11–13 — Partie la plus solide du manuscrit

L’identité

[
2^\rho-1=(2^\sigma-1)+2^\sigma(2^\tau-1)
]

et la partition en sept secteurs donnent une véritable preuve de la somme homogène, pas seulement une heuristique.

Le passage de la somme homogène au second moment est standard et correct.

La Section 13 fait un usage propre de Chen–Stein. Le facteur (1\wedge\lambda^{-1}) du théorème général peut être supprimé puisqu’il est au plus (1), et le terme (b\_3) est nul pour un graphe de dépendance exact.

## Section 14 — Correcte après une petite explicitation

Les masques déterministes suivent uniformément.

Le processus spatial est obtenu intelligemment par amincissement indépendant et convergence des probabilités de vide. Cela évite tout besoin d’une estimation à trois blocs.

Le processus marqué est également plausible. Il faut seulement ajouter l’observation sur les supports proches mais disjoints exposée plus haut.

## Section 15 — Plausible et conditionnelle aux sources externes

La coupure en trois zones est bien pensée :

1. petits (x) : nombreux pivots premiers intermédiaires ;
2. (x) polynomial en (L) : grands premiers de Laishram–Shorey ;
3. plus grandes hauteurs : rareté des paires de défauts par Pell, plus borne ponctuelle de Balasubramanian–Shorey.

Le double passage

[
M\to\infty\quad\text{puis}\quad j\_0\to\infty
]

est nécessaire et correctement respecté.

## Sections 16–17 — Plausibles, mais nécessitent la plus forte révision

Je n’ai pas trouvé d’exposant contradictoire dans les remplacements R1–R10. Le phénomène volumique (2:1) est correctement identifié.

Mais le volume de transports à vérifier est trop grand pour que quelques lignes « same proof after R1–R10 » constituent une présentation satisfaisante sans formalisation accessible.

Le théorème global repose entièrement sur ce point. C’est donc ici que je concentrerais la demande de révision.

## Section 18 — Déclaration utile, mais pas encore validation

Le papier est honnête sur plusieurs restrictions :

- sept ponts bibliographiques restent hypothétiques ;
- la convergence ponctuelle est une forme de Laplace ;
- le conditionnement est représenté extensionnellement ;
- certains énoncés sont mécanisés dans une variante légèrement différente.

Cette transparence est positive. Elle rend cependant inadéquates les formulations plus générales selon lesquelles tout aurait été « vérifié dans son intégralité ».

---

# 6. Modifications indispensables avant publication

Je demanderais au minimum les changements suivants.

### 1. Publier et figer réellement l’archive Lean

Elle doit comprendre :

- sources complètes ;
- `lake-manifest.json` ;
- versions exactes de Lean et Mathlib ;
- script de build ;
- audit des hypothèses ;
- fingerprints des sept énoncés externes ;
- hash du PDF correspondant ;
- log d’une exécution indépendante.

### 2. Fournir une table de correspondance lisible pour les sept hypothèses

Pour chacune :

- énoncé Lean exact ;
- énoncé publié exact ;
- substitutions de variables ;
- hypothèses éventuellement renforcées ;
- résultat du manuscrit qui la consomme.

### 3. Expliciter la jonction manquante de la Section 14.4

Ajouter le court argument :

[
r\_e+1<|x-y|\le Q
\quad\Longrightarrow\quad
\text{supports disjoints de diamètre total }\<Y\_Q,
]

donc aucun premier (p>Y\_Q) partagé, donc aucune arête.

### 4. Réécrire la Proposition 9.11

Rendre explicite le recours préalable à la Proposition 9.9.

### 5. Développer la Proposition 16.1

Au minimum, donner une preuve autonome détaillée des quatre endroits réellement modifiés :

- comptage des hôtes ;
- canaux rationnels, notamment (2:1) ;
- secteurs CRT ;
- fermeture terminale avec (C\_{\rm det}(\kappa\_0)) et (C\_{\rm term}(\kappa\_0)).

### 6. Séparer clairement trois niveaux de validation

Le texte devrait distinguer :

1. preuve mathématique dans le manuscrit ;
2. déduction Lean conditionnelle aux sept hypothèses ;
3. passages standards non mécanisés, par exemple la caractérisation par fonctionnelles de Laplace.

### 7. Corriger quelques formulations bibliographiques et terminologiques

Notamment :

- présentation du corollaire de Laishram–Shorey ;
- définition initiale de « maximal stretch » ;
- portée exacte de la formalisation.

---

# Conclusion de referee

Le papier n’a pas les caractéristiques d’un manuscrit manifestement faux : les identités locales sont cohérentes, les exposants se ferment, les principales spécialisations diophantiennes sont légitimes, et la partie Chen–Stein est propre. Je n’ai pas trouvé d’erreur qui réfute le Théorème 1.1.

En revanche, il serait prématuré d’accepter un résultat de cette ampleur sur la seule base du PDF actuel. La preuve globale dépend d’une longue chaîne d’uniformités, et la validation Lean annoncée — qui serait l’outil naturel pour sécuriser cette chaîne — ne peut pas être reproduite avec les éléments fournis.

**Recommandation finale : révision majeure / rejet avec resoumission.** Le résultat dyadique principal mérite d’être pris au sérieux ; les extensions marquées et globales sont plausibles ; la revendication de certification formelle et la présentation de l’extension à rapport borné doivent être substantiellement renforcées avant publication.