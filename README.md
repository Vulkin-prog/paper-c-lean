# Formalisation Lean du papier C

Ce dépôt accompagne le manuscrit :

> *Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages
> constantes d'une fonction aléatoire complètement multiplicative de
> Rademacher étendue*, Brice Pouly, version 7c, juillet 2026.

Empreinte SHA-256 du PDF analysé :
`23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336`.

## Statut

Ce dépôt est un **noyau formel compilable en cours d'extension**, et non encore une
certification du théorème principal. Il sépare volontairement :

1. les objets et lemmes effectivement prouvés par Lean ;
2. les obligations arithmétiques, probabilistes et diophantiennes restant à
   formaliser ;
3. les résultats externes qui ne peuvent pas être remplacés honnêtement par
   des axiomes si l'objectif est une certification.

Le code livré ne contient ni `sorry` ni axiome mathématique ajouté. La commande

```bash
rg -n '(^|[[:space:]])(sorry|axiom|admit|native_decide|unsafe|partial)([[:space:]]|$)' PaperC
```

doit donc rester vide. Cela certifie seulement les modules présents, pas les
69 pages du manuscrit.

La version Lean `0.41.0` conserve la fermeture de la chaîne interne du §14
et nettoie les anciennes routes publiques devenues redondantes. Les sommes
de Riemann dyadiques, les paramètres amincis spatial et marqué, le graphe de
dépendance marqué, ses deux termes de Stein--Chen, les transferts exacts
cylindre--loi source et la dé-troncation sont assemblés. Sous les quatre
entrées de littérature explicites Arratia--Goldstein--Gordon,
Evertse--Silverman, Halter--Koch et Nicolas--Robin, Lean prouve les limites
des fonctionnels de Laplace
\[
 \mathbb E e^{-\int g\,d\Xi_{N,L}}
 \longrightarrow
 \exp\!\left(-\lambda\int_1^2(1-e^{-g(t)})\,dt\right)
\]
et, pour tout cutoff fixe contenant le support discret des marques,
\[
 \mathbb E e^{-\int g\,d\widehat\Xi_{N,L}}
 \longrightarrow
 \exp\!\left(-\lambda\int_1^2
   \sum_{e\ge0}2^{-(e+1)}(1-e^{-g(t,e)})\,dt\right).
\]
Ici le membre de gauche marqué est lui aussi littéral : le module
`FullMarkedLaplaceTransfer` définit la fonctionnelle source complète en
sommant sur tous les excès finis. Dès que \(g(t,e)=0\) pour \(e>E\), Lean
prouve son égalité point par point, puis en espérance, avec la fonctionnelle
tronquée à laquelle s’applique l’argument fini de Stein--Chen. L’endpoint
public quantifie donc directement sur
`infiniteFullMarkedLaplaceExpectation`, et non sur un substitut tronqué.
La probabilité d’une marque \(>E\) a un `limsup` au plus
\(\lambda2^{-(E+1)}\), ce qui donne la tension uniforme finale. Ces
fonctionnels complets constituent la caractérisation formelle des deux PPP ;
mathlib ne fournissant pas encore un espace standard de mesures ponctuelles
avec topologie vague, le dépôt n’introduit pas un faux objet topologique
uniquement pour reformuler cette conclusion.

Le lemme 14.4, l’unicité presque sûre de l’excès,
\(J_{x,L}=\sum_eK_{x,e}\), le lemme 14.7 et les transferts de cylindres de la
v0.39 restent la base de cette fermeture. La loi du maximum du corollaire
14.8 est également conclue canoniquement. Pour le vecteur fini des comptes,
les lois source/retenue et leur couplage sont exacts.
`PrimeEncodedCountVector` injecte le vecteur dans les entiers positifs par
les puissances des premiers ; `PrimeEncodedCountLaplace` identifie
exactement la loi source poussée et ses transformées aux tests constants
\(s\log p_e\). `PoissonVectorMass` effectue le même calcul pour la cible
produit--Poisson, et `DirichletAtomConvergence` transforme la convergence de
toutes ces transformées en convergence de chaque atome. Le théorème
`corollary_fourteen_eight_counts` ferme ainsi le vecteur des comptes sous les
quatre seules entrées de littérature canoniques, sans prémisse de loi
retenue ni nouveau pont.

Le jalon Lean `0.38.0` a déchargé l’interface interne de Pell généralisé du
lemme 9.2. Le nouveau module `PaperC.Diophantine.GeneralizedPell` formalise
la traduction en idéaux principaux, le quotient de deux générateurs d’une
même fibre comme unité de Pell, la croissance exponentielle des unités, le
contrôle logarithmique par la hauteur, le comptage fini des orbites et la
réduction au noyau carré-libre. Il en déduit
`GeneralizedPellPolynomialBoxStatement` à partir de deux corollaires
classiques étroits et explicitement audités : la comparaison de conducteur
entre \(\mathbb Z[\sqrt D]\) et l’ordre maximal (Halter–Koch) et l’enveloppe
divisorielle (Nicolas–Robin). Le facteur \(\tau(|M|)^2\) n’est pas admis :
`QuadraticIdealDivisors` le prouve dans Lean par factorisation unique des
idéaux et théorie de décomposition quadratique. L’ancien pont
`PCv07c-L9.2-generalized-Pell` porte désormais
`status: discharged`.

La v0.39 resserre encore la frontière bibliographique :
`PaperC.Diophantine.PellDivisorEnvelope` part de l’inégalité logarithmique
directe de Nicolas--Robin sur le nombre de diviseurs. Lean prouve ensuite
la substitution de hauteur polynomiale, le traitement des petits arguments,
le carré du facteur divisoriel et l’absorption du compte logarithmique des
unités. L’ancienne enveloppe spécialisée
`NicolasRobinPellEnvelopeStatement` reste comme wrapper
`NR83-T1-divisor-bound` déchargé ; les endpoints canoniques prennent
désormais `NR83-T1-divisor-log-bound`.

La chaîne de masse mère dyadique identifie exactement
\[
  R_2(N,L)=R_{2,\kappa}(N,2N,L),
\]
conserve sur cette spécialisation les taux \(3/2\), \(7/4\), \(31/16\) et
\(5/3\) des secteurs à économie de puissance, puis transporte le gain
exponentiel de la branche non terminale dense. La somme des sept secteurs
donne directement
\[
  R_2(N,L)=O_C\!\left(
    \frac{N^2}{(\log\log N)^2}\right)
\]
sous Evertse--Silverman et les deux entrées externes précédentes.

Les entrées canoniques
`corollary_thirteen_ten_uniformBigO_canonical` et
`theorem_one_one_uniformBigO_canonical` ont pour liste exacte de ponts AGG,
Evertse--Silverman, la comparaison de conducteur de Halter–Koch et
Nicolas–Robin,
tous de nature `external`. Aucun pont `internal/open` ne remonte donc au
théorème 1.1 canonique : c’est le jalon « inconditionnel modulo littérature ».
La v041 supprime les anciennes signatures prenant directement Pell ou son
enveloppe spécialisée, ainsi que les quatre interfaces C11.3, P9.9, P9.11 et
T10.1 et leurs consommateurs publics. Les signatures canoniques restent
inchangées.

Cette version conserve aussi la fermeture sans pont des lemmes 17.14–17.16
et de l’instance \(\alpha=3/16\) de 17.17, ainsi que la population terminale
canonique
\[
  T_K=\{s+\widetilde k\le
    \lfloor K\sqrt B/\log B\rfloor\}
\]
Elle ferme maintenant les trois secteurs profonds de la proposition 16.1
sous les seules entrées externes déjà enregistrées : Evertse--Silverman,
Halter–Koch et Nicolas–Robin.

L’équivalence arithmétique du lemme 9.10 est désormais prouvée dans sa portée
source exacte. Lorsque
`canonicalReducedCandidate? x y (L + 1) ((L + 1) ^ A) = none`, le code
rationnel canonique est nul et les coordonnées corrigées de cardinal
\(D^\#+c^\#\) paramètrent tout l’espace des solutions des grands premiers.
Sous \(L+1\le M\), \(x+L\le M\) et \(y+L\le M\), Lean envoie la frontière
de chaque relation complète dans le noyau de la matrice concrète formée des
lignes des petits premiers et des deux parités de blocs. L’injectivité et la
surjectivité de ce morphisme sont prouvées, puis donnent l’équivalence
linéaire relations--noyau et, puisque le code rationnel est nul,
l’équivalence quotient résiduel--noyau. L’interface auditée de 9.10 est
conservée avec `status: discharged`.

Pour 17.26, Lean couvre la population active littérale par les bases \(x-1\)
de fenêtres contenant deux défauts et par les formes finies des composantes,
puis désintègre chaque fibre fixée par son coefficient carré-libre lisse.
Le degré un satisfait l’enveloppe \(N^{1/2+o(1)}\). Le degré deux est injecté
dans Pell lorsque son coefficient normalisé est au moins deux, et dans les
paires de diviseurs signées de \(\Delta^2\) lorsque ce coefficient vaut un.
Le degré au moins trois est injecté dans Evertse--Silverman. Les facteurs
factoriels contrôlant \(\omega(n)\), les sommes de diviseurs et la somme
Evertse--Silverman sont désormais prouvés uniformément \(N^{o(1)}\), puis
les degrés, les bases et les formes sont agrégés. Lean obtient ainsi
\[
  N^{3/2+o_{C,\kappa_0}(1)}
    =o_{C,\kappa_0}(N^2)
\]
sans interface propre à 17.26.

Pour 17.28, Lean suit la dichotomie littérale du manuscrit.
Lorsque \(3c^\#\le2B\), un compte direct des hôtes à composante de taille au
plus dix est assemblé depuis les fibres mobiles de degrés \(2\) et au moins
trois, sous Pell et Evertse--Silverman. Lorsque \(2B<3c^\#\), une composante
de taille deux existe. Lean formalise la paramétrisation des deux singletons,
la somme harmonique et le produit eulérien, puis établit un compte global
\[
  N\exp\!\left(C_{\rm term}\frac{\sqrt B}{\log B}\right).
\]
L’union globale sur les formes utilise le majorant sûr \(9B^4\), et non le
facteur \(B^2\) affiné de la preuve source ; cette perte polynomiale est
absorbée dans \(C_{\rm term}\) et ne change pas le taux. Après extraction de
\(2^{R_K(B)+1}\), le choix formalisé
\[
  K=\frac{2C_{\rm term}+1}{\log2}
\]
donne \(2C_{\rm term}<K\log2\) et le petit-oh requis, sans interface propre à
17.28.

Pour 17.30, Lean ferme l’incidence des premiers starts et la sommation
uniforme des fibres de partenaires sous Pell, remplace le compte des petites
parties par l’enveloppe de Chebyshev, puis prouve
\(\#T_K\le N^{3/4+o(1)}\) et
\(\sum_{T_K}(2^\tau-1)\le N^{7/4+o(1)}=o(N^2)\). Le transport entre la
population de rang et la population intrinsèque applique directement le
théorème non aligné de 9.10, sans hypothèse arithmétique fournie par
l’appelant. Les API canoniques de la proposition 16.1 et du théorème 16.2
construisent donc ce secteur elles-mêmes à partir de Pell.

Les trois interfaces historiques 17.26, 17.28 et 17.30 restent enregistrées
pour les deux assemblages génériques directs et la traçabilité, avec le
statut `discharged`; l’interface historique de 9.10 porte désormais le même
statut. L’API canonique n’en consomme aucune. La proposition 16.1 canonique
prend seulement Evertse--Silverman et les deux corollaires de littérature
qui reconstruisent Pell. La v041 retire les six adaptateurs sectoriels
intermédiaires et les variantes recevant directement Pell ; seuls les
endpoints canoniques et les assemblages génériques directs sont conservés.
La toolchain reste gelée en Lean/mathlib `v4.19.0`.

Pour le théorème 16.2, avec l’hypothèse source \(C>0\), Lean définit le
compte global \(Z_M\) sur un cylindre fini commun, prouve le couplage de
troncature, le recentrage de Poisson et le double passage dans l’ordre
\(j_0\) puis \(M\). Il obtient
\[
 d_{\rm TV}(\mathcal L(Z_M),\operatorname{Pois}(\Lambda_M))\to0,\qquad
 \Lambda_M=(1+o_C(1))M2^{-L},
\]
ainsi que \(\mathbb P(Z_M=0)=e^{-\Lambda_M}+o_C(1)\), sous les entrées
enregistrées de la proposition 15.5 et du passage à rapport borné.
L’invariance de la marginale et de la loi lors de l’agrandissement du
cylindre est une équivalence finie prouvée. Les modules à rapport borné
certifient désormais le cardinal et la masse des mauvais départs, les
petits-oh de \(b_1\) et de la moyenne de \(b_2\), le mélange des lois
conditionnelles, le couplage bon/complet, la moyenne retenue et son erreur
d’arrondi. `BoundedRatioPoissonAssembly` assemble ces résultats sous AGG et
la proposition 16.1, puis `TheoremSixteenTwo` les transporte exactement vers
le compte retenu et ferme le double passage. L’ancienne interface
interne agrégée `BoundedRangePoissonApproximation` est supprimée.

Le théorème public générique 16.2 conserve les trois interfaces sectorielles
pour un classifieur terminal arbitraire. Sa variante canonique principale ne
prend plus ni seuil \(K\), ni famille terminale, ni estimation de la section
17. Ses seules prémisses non formalisées sont PNT, Laishram--Shorey,
Balasubramanian--Shorey, AGG et Evertse--Silverman (`external`), ainsi que
les deux entrées externes qui déchargent Pell (Halter–Koch et
Nicolas–Robin). Elle n’ajoute aucune dette d’assemblage probabiliste ni
aucun pont interne ouvert. Les convergences PPP du §14 sont désormais
certifiées par leurs fonctionnels de Laplace et, pour les marques, par la
tension uniforme. Les métriques de publication sont reproduites dans
[`REPRODUCIBILITY.md`](REPRODUCIBILITY.md).

## Contrat d'archive

À partir de la version 0.19, toute archive publiée possède une unique racine
`paper_c_lean/`. Les fichiers du projet se trouvent immédiatement sous cette
racine. Ce contrat est stable pour les versions suivantes : ni archive à plat,
ni double emboîtement `paper_c_lean/paper_c_lean/`.

## Modules certifiés

- `PaperC.Arithmetic.ParityVector` : vecteur des valuations premières modulo
  deux et compatibilité avec la multiplication.
- `PaperC.Arithmetic.CRT` : un certificat de congruences deux à deux
  premières définit une classe unique modulo le produit, avec une interface
  certifiée entre `Nat.ModEq` et les congruences entières.
- `PaperC.Arithmetic.IntervalCongruence` : majorants exacts du nombre de
  représentants d'une classe dans un intervalle et dans un produit de deux
  intervalles, utilisés par les remplacements R3--R5.
- `PaperC.Arithmetic.CertificateCount` : composition de l'unicité CRT et du
  comptage d'intervalle, donnant directement le majorant
  « longueur / produit des moduli \(+1\) » pour un certificat fini, ainsi que
  sa forme rectangulaire à deux variables. Sous \(P\le N\) et pour des
  intervalles de longueur au plus \(C_0N\), Lean absorbe aussi le terme
  terminal et obtient \((C_0+1)N/P\), respectivement son carré.
- `PaperC.Arithmetic.StartResidue` : classe résiduelle canonique d'un offset
  de start et équivalence exacte
  \(x\equiv r_{p,v}\pmod p\iff
  p\mid\operatorname{label}(x,v)\), qui relie les cellules arithmétiques au
  CRT naturel.
- `PaperC.Arithmetic.ChannelGeometry` : géométrie entière d'un canal,
  direction primitive de la différence de deux cellules et bornes
  \(a,b\le L\).
- `PaperC.Arithmetic.ChannelUniqueness` : argument déterminant exact donnant
  l'unicité de deux codes rationnels réduits dans un canal assez étroit
  (cœur arithmétique du lemme 5.2).
- `PaperC.Arithmetic.ChannelCount` : projections injectives des cellules d'un
  canal et majorant exact par le plus grand pas primitif, soit le facteur
  géométrique \(1+B/\max(a,b)\) du lemme 7.2.
- `PaperC.Arithmetic.ResidualChannelCells`, `ResidualChannelCount`,
  `ResidualChannelSupport`, `ResidualPrimeMass`,
  `DyadicPrimeReciprocalSums` et `ResidualChannelLemmaSevenTwo` :
  définition exacte de \(\Delta=h+bj-ai\), des cellules résiduelles
  \(p\mid\Delta\ne0\), de leur support premier fini et de leurs fibres par
  valeur de \(\Delta\). Lean prouve
  \[
  E_p\le
  \left(1+\frac{8qB}{p}\right)\left(1+\frac Bq\right),
  \qquad p<4qB,
  \]
  puis, par coquilles dyadiques et la borne de Chebyshev déjà certifiée,
  \[
  \sum_p\frac{E_p}{p}\le
  \frac{896B}{\lfloor\log_2B\rfloor}.
  \]
  Le support choisi est démontré complet : tout agrandissement du cutoff
  premier n'ajoute que des termes nuls. Cela certifie le lemme 7.2 dans une
  formulation finie effective, sous les hypothèses explicites du papier
  \(m\ge2\), \(2\le q\le L\) et \(B=L+1\ge4\).
- `PaperC.Affine.StartBoundaryRange`, `RelationBoundaryIff` et
  `RationalChannelCode` : la frontière complète est exactement
  l'hyperplan des vecteurs pairs; les équations premières caractérisent
  exactement les relations; les sous-ensembles pairs des unités d'un canal
  donnent un code injectif de dimension \(m-1\), avec critère de non-nullité
  \(m\ge2\) et caractère affine
  \(1_{\{i=-1\}}+1_{\{j=-1\}}\). Cela certifie le lemme 5.1.
- `PaperC.Arithmetic.CanonicalChannel`,
  `PaperC.Asymptotics.CanonicalChannelWindow`,
  `PaperC.Affine.CanonicalRationalCode` et
  `PaperC.Asymptotics.CanonicalRationalCodeWindow` : sélection finie du
  rapport réduit canonique, unicité uniforme par déterminant, construction
  de \(S_{\rm rat}\), \(\sigma,\tau\), branche exacte \(m_{\rm ex}\le1\), et
  couverture de tout code non nul. Cela certifie le lemme 5.2.
- `PaperC.Arithmetic.ChannelEnumeration`,
  `ChannelMultiplicityBounds`, `ChannelStartPairs`,
  `SeparatedSmallChannels`, `HeightTwoPairCount`,
  `WeightedChannelMass` et `RationalMassFinite`, avec les modules
  asymptotiques `CriticalChannelPowers`, `RationalPowers`,
  `CriticalRationalMassEnvelopes`, `CriticalRationalMass` et
  `WeightedChannelMassCritical` : comptages finis des rapports, hauteurs,
  unités et couples de starts, traitement frontal \(q=2\), puis preuves
  uniformes \(N^{4/3+o_C(1)}\), \(N^{5/3+o_C(1)}\) et
  \(N^{1+o_C(1)}\). Ils certifient la proposition 5.4 et le lemme 5.5.
- `PaperC.Combinatorics.LargePrimeOccurrences`,
  `LargePrimeGraph`, `PinnedGraphResolution` et
  `LargePrimeGraphResolution` : construction du graphe des grands premiers,
  identification exacte de ses équations avec \(W_{>B}(x,y)\), puis
  équivalence linéaire canonique avec une coordonnée libre par composante non
  épinglée. Lean prouve
  \(\dim W_{>B}=D+c\), identifie \(D\) au nombre littéral de sommets
  défectueux et obtient \(D+2c\le2(L+1)\). Cela certifie entièrement le
  lemme 6.1.
- `PaperC.Arithmetic.ComponentSquareClass` et
  `PaperC.Combinatorics.LargePrimeComponents` : sur toute composante non
  épinglée de deux starts positifs séparés, les parités aux premiers
  \(p>L+1\) s'annulent et le produit des labels s'écrit
  \(d z^2\), où \(d>0\) est carré-libre et tous ses diviseurs premiers sont
  \(\le L+1\). Le représentant \(d\) et la racine positive sont canoniques et
  uniques. Cela certifie la conclusion de classe carrée du lemme 6.2.
- `PaperC.Arithmetic.ExactUnitLargeKernel` et
  `PaperC.Combinatorics.ExactUnitIsolation` : pour une unité exacte dont les
  coefficients primitifs sont sous le cutoff, les deux occurrences ont le
  même noyau impair grand. Si ce noyau vaut un, elles sont toutes deux
  défectueuses; sinon elles sont adjacentes et forment à elles seules une
  composante non épinglée de cardinal deux. Deux unités distinctes d'un même
  canal positif ont en outre des paires d'occurrences disjointes et
  déterminent des composantes distinctes; dans la branche non défective,
  celles-ci restent non épinglées et de cardinal deux. Cela certifie
  entièrement le lemme 6.3 sous ses hypothèses explicites de positivité,
  coprimalité, hauteur et cutoff.
- `PaperC.LinearAlgebra.QuotientParity`,
  `CanonicalResidualQuotient`,
  `PaperC.Combinatorics.LargePrimeRelationBoundary`,
  `ResidualComponentCounts` et `DefectiveVertexIntervalBound` :
  interprétation littérale de \(\tau\) comme dimension de
  \(R(x,y)/S_{\rm rat}\), injection de la frontière des relations dans
  \(W_{>B}\), perte d'une dimension par la parité du bloc gauche, partition
  \(m=d+n\), définitions exactes de \(D^\#\) et \(c^\#\), puis
  \[
  \tau\le D^\#+c^\#,\qquad D^\#+2c^\#\le2B.
  \]
  Les sommets défectueux sont injectés dans les deux ensembles de défauts
  d'intervalle; la proposition 3.2 donne ensuite, avec quantificateurs
  uniformes sous la fenêtre critique,
  \(D^\#\ll_C B/\log B\). Cela certifie le lemme 6.4 dans le modèle fini,
  sous les hypothèses géométriques explicites du papier.
- `PaperC.Combinatorics.ResidualCertificates`,
  `OneUnitResidualExceptions`, `CanonicalResidualComponents`,
  `CanonicalResidualPrimeProduct` et
  `CanonicalResidualCRTCertificate` :
  construction concrète de \(C_{\rm res}\), preuve
  \(\lvert C_{\rm res}\rvert=c^\#\), choix du plus petit premier puis de la
  cellule lexicographiquement minimale dans chaque composante, et famille
  canonique de cardinal \(c^\#\). Lean vérifie que les offsets gauches sont
  distincts, que les offsets droits le sont aussi, que les premiers
  \(p_s>B\) sont distincts, qu'ils divisent \(x+i_s\) et \(y+j_s\), et que
  \(h+bj_s-ai_s\ne0\) lorsque \(m\ge2\). Lorsque \(m=1\), toute exception
  appartient à la famille des composantes rencontrant les deux occurrences
  de l'unique unité, dont le cardinal est au plus deux. Cela certifie le
  lemme 6.5. Le produit canonique \(P^\#\) est en outre défini, positif, possède
  exactement \(c^\#\) facteurs et porte une dichotomie formelle
  \(P^\#\le N\) / \(P^\#>N\). Le certificat complet associé a ce produit,
  est admissible exactement dans la première branche, et les deux starts
  satisfont toutes ses congruences.
- `PaperC.Affine.System` : systèmes affines finis sur
  \(\mathbf F_2\), compatibilité, fibres et comptage exact par le noyau.
- `PaperC.Affine.Probability` et `PaperC.Affine.Fourier` : probabilité
  uniforme exacte d'une fibre et identité de Fourier division-free du
  lemme 2.1.
- `PaperC.Affine.Normalization` : caractère des relations, paramètres
  \(\eta,\rho\), normalisation exacte de la somme signée et inégalité
  \(\lvert\eta2^\rho-1\rvert\le 2^\rho-1\) du lemme 2.1.
- `PaperC.Combinatorics.TreeBoundary` : frontière d'un ensemble fini
  d'arêtes, additivité par différence symétrique, existence sur un graphe
  connexe et bijection existence--unicité entre sous-ensembles d'arêtes d'un
  arbre et parties paires de sommets (lemme 2.2).
- `PaperC.Combinatorics.CertificateSummation`,
  `CertificateCRTInstantiation`, `CertificateCellFamilies` et
  `CertificateLemmaSevenOne`, avec
  `PaperC.Analysis.ExponentialSeriesMajorant` : passage des certificats
  ordonnés aux certificats non ordonnés, premiers distincts donc copremiers,
  condition \(P\le N\), comptes CRT pondérés 1D/2D, facteur exact \(1/r!\),
  regroupement des cellules donnant \(u\sum_pE_p/p\) et
  \(uM\sum_p1/p^2\), sommation sur toutes les tailles possibles et
  majoration par la série exponentielle. Cela certifie le lemme 7.1 dans sa
  formulation finie exacte.
- `PaperC.Combinatorics.ResidualMasses`,
  `PropositionSevenThreeSigmaZeroCover`,
  `PositiveSigmaFixedChannelCover`, `PositiveSigmaFixedChannelBound`,
  `PositiveSigmaGlobalGrouping` et `PositiveSigmaKeyMassBound`, avec les
  modules asymptotiques `CorrectedDefectEnvelope`,
  `SigmaZeroQuadraticCritical`, `ResidualCertificateMassCritical`,
  `PositiveSigmaQuadraticCritical`, `QuadraticAndInterpolationClosure` et
  `PropositionSevenThreeCritical` : définition littérale des masses
  \(Q_{\rm res}\) et \(R_{\rm res}\) du secteur \(P^\#\le N\), partition
  exacte selon \(\sigma=0\) ou \(\sigma>0\), couverture CRT bidimensionnelle
  de la branche exceptionnelle, puis regroupement sans double comptage de la
  branche systématique par les clés finies \((q,a,b,h,r)\). Les enveloppes
  explicites utilisent respectivement
  \(\exp(112B/\lfloor\log_2B\rfloor)\) et
  \(\exp(3584B/\lfloor\log_2B\rfloor)\), ainsi que le maximum fini du défaut
  corrigé. Lean en déduit, uniformément dans la fenêtre critique,
  \[
  Q_{\rm res}\le N^{2+o_C(1)},\qquad
  R_{\rm res}\le N^{7/4+o_C(1)},
  \]
  la seconde borne étant obtenue par l'interpolation finie (6.6). Cela
  certifie entièrement la proposition 7.3 sous ses hypothèses explicites.
- Les modules `SmallHeightLargeProductPairs`,
  `SmallHeightResidualPrimeSupport`, `SmallHeightResidualComponentEnvelope`,
  `SmallHeightTauEnvelope` et `SmallHeightLargeProductMassBound`, avec les
  modules asymptotiques `SmallHeightComponentEnvelopeCritical`,
  `SmallHeightTauEnvelopeCritical`, `SmallHeightSigmaZeroCritical`,
  `SmallHeightPositiveSigmaCritical` et `PropositionSevenFourCritical`,
  formalisent le secteur \(P^\#>N\) de petite hauteur canonique
  \(q\le\sqrt{\log(L+1)}\). Lean construit une enveloppe finie du nombre de
  composantes résiduelles, sépare exactement les branches \(\sigma=0\) et
  \(\sigma>0\), puis démontre, pour \(C\ge0\) et \(A\ge1\), uniformément dans
  la fenêtre critique,
  \[
  Q_{\rm res}^{\rm petite\ hauteur}\le N^{5/3+o_C(1)},\qquad
  R_{\rm res}^{\rm petite\ hauteur}\le N^{19/12+o_C(1)}.
  \]
  La seconde majoration implique en particulier
  \(R_{\rm res}^{\rm petite\ hauteur}=o_C(N^2)\). Cela certifie la
  proposition 7.4 sous ses hypothèses explicites, sans affirmer
  d'équivalence asymptotique ni certifier le théorème principal.
- `PaperC.Combinatorics.SmallComponentExtraction`,
  `AlignedExactFreeComponents`, `ComponentProductParity`,
  `AlignedRungeBridge`, `AlignedCoreExclusion`,
  `AlignedDeepCoreExtraction` et les modules de code
  `TwoParityColumnCode`, `AlignedComponentCode`,
  `AlignedComponentHamming` certifient le cœur fini du théorème 8.1.
  Lean retire au plus deux composantes rencontrant les unités exactes,
  extrait une famille de petites composantes, construit la matrice
  \(\Phi\) avec ses deux parités de blocs, trouve un mot court, en déduit un
  produit carré et des racines distinctes, puis applique Runge. Pour le cœur
  profond de la partition déjà certifiée, \(B\ge32\) et
  \(3B<16c^\#\) donnent explicitement au moins \(B/16\) composantes
  exact-free de taille au plus \(43\). Le rayon entier
  \[
  t(B)=\left\lceil
    \frac{64B}{\lfloor\log_2B\rfloor
      \lfloor\log_2\lfloor\log_2B\rfloor\rfloor}
  \right\rceil
  \]
  satisfait uniformément le budget de Hamming. Lean ferme aussi
  \(2R\le ax\) et toute la plage des inégalités de Runge
  \(1\le k\le43t(B)\), puis prouve finalement qu'aucun cœur aligné
  \(3B<16c^\#\), de hauteur \(H\le B^A\), ne subsiste pour \(N\) assez
  grand dans \(\lvert L-\log_2N\rvert\le C\).
- `PaperC.Diophantine.EvertseSilvermanInput` formalise l'interface exacte du
  lemme 9.1 sans transformer le résultat cité en déclaration globale. Le
  pont externe est une hypothèse explicite sur les abscisses \(X\) pour
  lesquelles \(Z^2=e\prod_r(X+h_r)\) possède une solution \(Z\ne0\), avec le
  majorant \(7^{4+9|S|}\). Lean prouve qu'il existe au plus deux ordonnées
  pour chaque abscisse, retrouve donc le facteur deux de (9.2), prouve
  séparément qu'il existe au plus \(d\) solutions avec \(Z=0\), puis utilise
  l'injection
  \((X,Y)\mapsto(X,eY)\) pour obtenir le majorant correspondant pour
  \(\prod_r(X+h_r)=eY^2\). Cette implication est certifiée ; le théorème
  d'Evertse--Silverman lui-même reste à importer ou à formaliser.
- `PaperC.Diophantine.PellInput` et
  `PaperC.Diophantine.PellRealExponent` formalisent les réductions des
  lemmes 9.2 et 17.19 pour tout exposant
  \(K_0\in\mathbb R_{>0}\). `GeneralizedPell`,
  `QuadraticIdealDivisors` et `PellDivisorEnvelope` déchargent le pont
  interne : idéaux, orbites d’unités, hauteurs et enveloppe divisorielle
  sont reconstruits en Lean à partir des seules entrées externes
  Halter--Koch et Nicolas--Robin. Lean prouve aussi l'injection
  \((z,w)\mapsto(Az,w)\), l'identité avec
  \(X^2-ACw^2=Ae\), la non-carréité de \(AC\), toutes les bornes de hauteur
  et le transfert exact du cardinal. Lean passe à
  \(J=\lceil K_0\rceil\), puis choisit
  \(H=\lfloor N^{K_0}\rfloor\) afin d’obtenir exactement le prédicat source
  \(|z|,|w|\le N^{K_0}\). Cette adaptation n’ajoute aucune hypothèse
  diophantienne.
- `PaperC.Diophantine.ComponentNormalization` et
  `SingletonProductParametrization` certifient les noyaux arithmétiques des
  lemmes 9.3--9.5. Lean construit le facteur carré-libre canonique de
  \(PQ=dz^2\), prouve son unicité et la borne \(e\le dP\), traite exactement
  le degré un, réduit injectivement le degré deux à Pell et le degré au moins
  trois à l'interface Evertse--Silverman, puis établit la paramétrisation
  canonique
  \(X=ecu^2,\ Y=(d/e)cv^2\), sa réciproque, son unicité et les bornes de ses
  paramètres. `BoundedRatioManyDefectsDegreeTwoSum`,
  `BoundedRatioManyDefectsEvertseSum` et
  `BoundedRatioManyDefectsDegreeAssembly` assemblent désormais les
  sommations asymptotiques de 9.4--9.5, sous Evertse--Silverman et le pont
  Pell déchargé ; seules les entrées de littérature restent ouvertes.
- `PaperC.Combinatorics.DeepCoreSmallComponent` et
  `PaperC.Diophantine.MultipleDefects` certifient les réductions finies des
  lemmes 9.6--9.8 : extraction d'une composante de taille bornée sous une
  hypothèse de densité, injection de deux défauts vers une équation de Pell,
  transfert exact du cardinal et factorisation de la branche de même classe.
  `BoundedRatioNonterminalHostCounts`,
  `BoundedRatioNonterminalRealHosts` et
  `BoundedRatioNonterminalAssembly` ferment le raccord aux populations
  d'hôtes et les sommes sur les paramètres lisses, sous les mêmes entrées.
- `PaperC.Asymptotics.PropositionNineNine` définit la population exacte du
  cœur profond avec \(\sigma=0\) et \(D^\#\ge3\), prouve les enveloppes
  finies de poids et de masse et retire les paires de masse nulle. Chaque
  hôte actif porte une composante canonique de support entre 2 et 10 et
  appartient à l’une des deux branches orientées possédant deux défauts
  concrets. La v041 supprime l’ancienne interface de compte d’hôtes et son
  endpoint asymptotique : la route canonique de masse mère utilise à la place
  les comptes directs à rapport borné. L’API arbitraire à formes fixées de
  9.9 n’est plus revendiquée comme endpoint public.
- `PaperC.LinearAlgebra.NonalignedCoreRank`,
  `PaperC.LinearAlgebra.CanonicalExactRank`,
  `PaperC.LinearAlgebra.CanonicalSmallRows`,
  `PaperC.Combinatorics.TerminalComponentCount` et
  `PaperC.Arithmetic.TerminalMatching` formalisent les noyaux des lemmes
  9.10--9.12. Lean construit les familles canoniques de cardinal
  \(D^\#\) et \(c^\#\), puis la vraie matrice des petites lignes, à
  \(\pi(L+1)+2\) lignes : premiers \(p\le L+1\) et deux parités de blocs.
  Sous \(L+1\le M\), les colonnes synthétisent injectivement des solutions
  concrètes des grands premiers, et leur noyau est exactement caractérisé par
  les frontières uniques de relations. Dans la branche source non alignée
  `canonicalReducedCandidate? = none`, Lean prouve que la synthèse des
  coordonnées est surjective sur tout l’espace des grands premiers. Sous les
  couvertures \(x+L\le M\) et \(y+L\le M\), les frontières complètes
  donnent alors une équivalence linéaire entre relations et noyau concret.
  Le code rationnel étant nul, cette équivalence descend au quotient
  résiduel et prouve sans pont
  \(\tau+\widetilde k=D^\#+c^\#\). Le compte combinatoire donne au moins
  \(B-3s\) composantes de taille deux ; leurs noyaux sont non triviaux, égaux
  dans une composante, premiers entre composantes, et leur produit divise un
  déterminant non nul borné explicitement.
- `PaperC.Arithmetic.TerminalKernelCount`,
  `PaperC.Combinatorics.CanonicalTerminalPopulation`,
  `PaperC.Combinatorics.TerminalClosureCounting` et
  `PaperC.Diophantine.TerminalPartnerPell` certifient les étapes finies de la
  proposition 9.11 et de la fermeture terminale du théorème 10.1. Pour
  \(s=B-c^\#\), la famille résiduelle canonique possède au moins \(B-3s\)
  composantes de taille deux. Un proxy fini de \(T_K\), paramétré par la
  fonction représentant \(\widetilde k\) et par un budget entier, est
  raccordé aux fibres de premiers départs et de partenaires ; Lean prouve
  \(\tau\le B+2\) et
  \(\mathrm{masse}(T_K)\le\#T_K\,4\,2^B\). S'y ajoutent l'unicité du facteur
  au-dessus du seuil, le double comptage, la réduction injective des
  partenaires à Pell, et
  \[
  \#A_{B,T}(X)\le
  2\sqrt X\sqrt T\prod_{p\le B}(1+p^{-1/2})
  \le2\sqrt X\sqrt T\,e^{2\sqrt B}.
  \]
  Le compte des partenaires est conditionnel aux deux entrées externes qui
  reconstruisent Pell. Les majorants asymptotiques des premières
  coordonnées et des fibres ainsi que l’assemblage canonique sont maintenant
  fermés. L’ancien wrapper générique de T10.1 est supprimé en v041.
- `PaperC.Combinatorics.SectionElevenPartition` et
  `CanonicalSectionElevenPartition` formalisent les six tests ordonnés du
  lemme 11.1. Les sept secteurs couvrent toutes les paires séparées, sont
  deux à deux disjoints et déterminent un secteur unique. Les trois premiers
  coïncident exactement avec les populations déjà certifiées de la section
  7, et l'union des quatre derniers est exactement le cœur profond. Le
  second module instancie le test terminal par le proxy à budget entier et
  identifie exactement le secteur 7 à sa partie canoniquement non alignée ;
  l'identification de la fonction de rang et du budget au seuil asymptotique
  du manuscrit reste explicite.
- `PaperC.Asymptotics.PropositionElevenTwo` conserve le noyau fini de la
  proposition 11.2. Lean prouve l'identité
  \(2^{\sigma+\tau}-1=(2^\sigma-1)+2^\sigma(2^\tau-1)\), les sommes finies
  associées et la désintégration dans les sept secteurs. Les secteurs 1–5
  sont raccordés aux propositions 7.3–7.5, au théorème 8.1 et à la
  proposition 9.9. La v041 retire l’ancien assemblage public paramétré par
  `smallRowRank` et `rankBudget`, ainsi que ses trois interfaces internes.
  La conclusion uniforme utilisée par les endpoints canoniques est désormais
  fournie exclusivement par la masse mère quantitative à rapport borné.
- `PaperC.Asymptotics.PropositionElevenThree` conserve le calcul des cinq
  secteurs élémentaires et le calcul d’assemblage à l’échelle littérale du
  corollaire 11.3,
  \[
    R_2(N,L)\ll_C N^2
      \exp\!\left(-c\frac{\sqrt{\log N}}{\log\log N}\right).
  \]
  Les anciennes conclusions publiques consommant le taux abstrait du sixième
  secteur, le compte d’hôtes 9.9 et la masse terminale 10.1 sont supprimées.
  `DyadicKappaQuantitative` fournit directement la conclusion canonique.
- `PaperC.Probability.SectionTwelveMoments` conserve le noyau exact de la
  déduction des moments du §12 dans le cylindre fini. Les paires hors
  diagonale sont partitionnées en chevauchement strict, contact et
  séparation ; Lean prouve les identités exactes du second moment factoriel,
  \[
  \mathbb E[(Z)_2]-(N)_2\,2^{-2L}=o_C(1),\qquad
  \mathbb E[(Z)_2]-\lambda_N^2=o_C(1),
  \]
  et de la variance à partir d’une estimation homogène fournie. Les trois
  anciens endpoints publics qui recevaient les interfaces de 9.9, 9.11 et
  10.1 sont supprimés ; la v041 ne revendique plus cette route legacy comme
  endpoint autonome du théorème 1.4.
- `PaperC.Analysis.TerminalPrimeCutoff`,
  `PrimeReciprocalSqrtSum`, `PaperC.Probability.BadStartCount` et
  `TerminalBadStartBound`, puis `BadStartMass`, formalisent les noyaux des
  lemmes 13.3–13.4. Le seuil est
  littéralement \(Y=\lfloor B^2\log B\rfloor\), avec \(B\le Y\le B^3\)
  pour \(B\ge2\).
  Lean injecte les incidences de mauvais starts et conserve le produit
  eulérien exact. Une décomposition dyadique fondée uniquement sur la borne
  de Chebyshev certifiée donne, pour \(H\ge16\),
  \[
  \sum_{p\le H}p^{-1/2}\le
  2\sqrt{\operatorname{rootCutoff}(H)}
  +\frac{56\sqrt{2H}}{\lfloor\log_2H\rfloor/2},
  \qquad \operatorname{rootCutoff}(H)^2\le H.
  \]
  Pour \(N\ge1\) et \(B\ge16\), cette estimation donne sans pont au seuil
  terminal l'enveloppe explicite
  \[
  \#D_Y\le2L\sqrt{2N+L}\,
  \exp\!\left(
    2\sqrt{\sqrt{B^2\log B}}+
    168\sqrt2\,\frac B{\sqrt{\log B}}\right).
  \]
  Les modules `TerminalBadStartsCritical` et `BadStartMassCritical`
  ferment les deux raccords : l'exponentielle terminale est uniformément
  sous-polynomiale, donc
  \(\#D_Y=N^{1/2+o_C(1)}\), \(\#D_Y=o_C(N)\) et
  \(2^{-L}\#D_Y=o_C(1)\). De plus,
  `terminalDefectWeightMass` est dominée exactement par la masse de défauts
  de la proposition 3.2. Lean conclut ainsi
  \(\sum_{x\in D_Y}\mathbb P(J_{x,L}=1)=o_C(1)\), sans pont.
- `PaperC.Probability.LargePrimeDependencyGraph` et
  `PaperC.Analysis.DependencyEdgeBound`, puis
  `PaperC.Asymptotics.DependencyEdgesCritical`, construisent les supports
  \(\Pi_x(Y)\), le graphe simple des bons starts et sa couverture par un
  premier partagé. Ils donnent
  \[
  E_Y\le(L+1)^2\sum_{\substack{Y<p\le3N\\p\ {\rm premier}}}(N/p+1)^2
  \]
  puis le majorant entièrement explicite
  \[
  (L+1)^2\left(
    \frac{28N^2}{Y\lfloor\log_2Y\rfloor}
    +\frac{6N^2}{Y}+3N\right).
  \]
  Au cutoff littéral \(Y=\lfloor(L+1)^2\log(L+1)\rfloor\), Lean le réduit à
  \(E_Y\le37N^2/m\) dès \(m\le\log(L+1)\), puis prouve uniformément
  \(E_Y=o_C(N^2)\) dans la fenêtre critique, sans aucun pont.
  La conclusion asymptotique (13.6) est donc certifiée ; la formule plus
  précise du manuscrit contenant \(NB^2\log\log N\) n'est pas reproduite,
  car le majorant intermédiaire plus grossier suffit au petit-oh.
- `PaperC.Probability.ConditionalDependencyGraph` et
  `ConditionalAGGInstantiation` ferment le lemme 13.5 et son raccord à
  l’interface AGG dans le cylindre fini. Lean prouve que chaque événement
  conditionné dépend seulement de \(\Pi_x(Y)\), puis sa factorisation contre
  l’événement joint d’une famille arbitraire de bons non-voisins. La loi
  uniforme des coordonnées restantes est une `FinitePMF`; sa marginale vaut
  exactement \(2^{-L}\). Pour tout start, tout ensemble extérieur et toute
  affectation booléenne de cet ensemble — pas seulement le motif où tous les
  événements sont vrais — Lean prouve la factorisation requise par
  `HasExactDependencyGraph`. L’application du pont externe AGG au cylindre
  concret est donc un théorème Lean direct.
- `PaperC.Probability.ArratiaGoldsteinGordonInput` enregistre le théorème
  13.7 comme pont `external`. Il définit une famille finie d'indicatrices,
  les voisinages fermés, l'indépendance exacte hors voisinage, \(b_1,b_2\),
  la loi de la somme et la distance totale à la loi de Poisson. La
  conséquence \(d_{\rm TV}\le2(b_1+b_2)\) n'est jamais postulée : elle doit
  être fournie explicitement comme hypothèse citée.
- `PaperC.Probability.SteinChenTerms` et
  `PaperC.Asymptotics.SteinChenCritical` formalisent le lemme 13.8.
  Le premier terme vérifie inconditionnellement \(b_1=o_C(1)\). Le second
  est décomposé en chevauchement, contact et séparation ; son majorant fini
  et \(\mathbb E b_2=o_C(1)\) sont prouvés sous la conclusion de la
  proposition 11.2 fournie comme prémisse explicite.
  `PaperC.Probability.ConditionalAGGAverage` prouve la décomposition exacte
  `SampleSpace ≃ SmallSample × LargeSample`, puis la loi totale uniforme.
  Les moyennes conditionnelles de \(b_1\) et \(b_2\) sont ainsi identifiées
  exactement aux termes finis de 13.8, sans nouveau pont.
  `PaperC.Probability.SectionThirteenFiniteBound` ajoute le calcul autonome
  de variation totale : symétrie, triangle, convexité d’un mélange uniforme
  et inégalité de couplage entre lois naturelles finies. Ensemble, ces
  modules donnent le majorant fini explicite du corollaire 13.9 à partir des
  mauvais starts et des termes de Stein–Chen.
  La v041 retire l’ancien endpoint qui reconstruisait cette prémisse à partir
  des trois interfaces internes de 11.2.
  `PaperC.Probability.SectionThirteenCouplings` identifie ensuite la loi
  moyenne à la loi du bon compte sur le cylindre complet, couple celui-ci au
  compte de tous les starts, et prouve directement
  \(d_{\rm TV}(\mathrm{Pois}(r),\mathrm{Pois}(s))\le|r-s|\). La différence
  des paramètres vaut exactement \(\#D_Y2^{-L}\).
  La route quantitative canonique assemble directement la conclusion plus
  forte du corollaire 13.10 :
  \[
    d_{\rm TV}\!\left(\mathcal L(Z_{N,L}),
      \mathrm{Pois}(N2^{-L})\right)=o_C(1).
  \]
  Les anciens endpoints qualitatifs autonomes du corollaire 13.9 et le
  transport sectoriel abstrait de 11.3 sont supprimés ; les lemmes finis et
  les raccords canoniques restent disponibles.
  Lean prouve notamment
  \[
    e^{-c\sqrt{\log N}/\log\log N}
      =O_c((\log\log N)^{-2})
  \]
  Il établit aussi ce taux pour le cardinal normalisé des mauvais starts, la
  contribution pondérée des défauts terminaux et leur masse de probabilité
  complète. `PaperC.Asymptotics.DyadicKappaTransport` identifie la masse
  mère à la spécialisation \(M=2N\) de \(R_{2,\kappa}\).
  `BoundedRatioElementaryQuantitative`, `BoundedRatioDenseQuantitative` et
  `DyadicKappaQuantitative` préservent les taux sectoriels, assemblent les
  branches modérée et dense du sixième secteur et somment les sept masses.
  `PaperC.Asymptotics.CorollaryThirteenTen` spécialise ensuite la borne
  harmonique des arêtes au cutoff terminal, prouve leur taux critique,
  reconstruit quantitativement \(b_1\) et \(\mathbb E b_2\), applique AGG
  puis assemble le triangle final de variation totale. Lean obtient ainsi
  \[
    d_{\rm TV}\!\left(\mathcal L(Z_{N,L}),
      \operatorname{Pois}(N2^{-L})\right)
      =O((\log\log N)^{-2})
  \]
  uniformément dans \(\lvert L-\log_2N\rvert\le C\). L’entrée canonique
  dépend seulement d’AGG, d’Evertse--Silverman, de Halter--Koch et de
  Nicolas--Robin. Les anciennes entrées sectorielles et Pell directes sont
  supprimées. La formule intermédiaire plus fine de 13.6 n'est pas
  revendiquée : la borne harmonique plus grossière suffit au taux final.
- `PaperC.Probability.MaskedFirstMoment` et
  `PaperC.Asymptotics.MaskedFirstMomentCritical`, avec
  `PaperC.Asymptotics.LogLogRunWindow`, ferment uniformément le premier
  moment de la proposition 14.1 pour tous les masques déterministes dans la
  fenêtre littérale
  \(\lvert L-\log_2N\rvert\le C_\star\log\log N\). L’enveloppe obtenue est
  \(N^{-1/2+o(1)}\), donc uniformément \(o(1)\), sans pont.
- `PaperC.Probability.MaskedSteinChen`,
  `PaperC.Asymptotics.MaskedPoissonCritical` et
  `PaperC.Asymptotics.MaskedPoissonCanonical` ferment la proposition 14.2
  modulo littérature seulement. Le graphe original reste un graphe de dépendance exact
  après annulation déterministe des indicatrices hors masque ; ses termes
  \(b_1,b_2\) sont dominés par leurs versions complètes. Lean identifie la
  loi conditionnelle moyenne à la loi du compte masqué sur le cylindre
  complet, couple ce compte après retrait de \(D_Y\), contrôle exactement la
  perte de paramètre puis prouve, uniformément pour tout
  \(A_N\subseteq I_N\),
  \[
    d_{\rm TV}\!\left(\mathcal L(Z_{N,L}(A_N)),
      \operatorname{Pois}(|A_N|2^{-L})\right)=o_C(1).
  \]
  L’endpoint canonique prend exactement AGG, Evertse--Silverman,
  Halter--Koch et Nicolas--Robin. Les anciennes interfaces internes de la
  proposition 11.2 et leurs wrappers publics sont supprimés en v041 ; la
  signature canonique est inchangée.
- `PaperC.Probability.SpatialThinningFinite`,
  `IndependentThinning`, `LaplaceVoidClosure` et
  `PoissonLaplaceFunctional` construisent la loi produit des variables
  auxiliaires de Bernoulli et prouvent l'identité finie
  \[
    \mathbb P(W_g=0\mid(J_x)_x)
      =\exp\!\left(-\sum_{x:J_x=1}g_x\right),
  \]
  ainsi que les dominations des termes amincis et l’erreur AGG
  \(4(b_1+b_2)\). `SpatialRiemannSums`,
  `SpatialMarkedParameters`, `ConditionalExpectationAverage`,
  `InfiniteLaplaceTransfer` et `SpatialLaplaceCritical` raccordent cette
  identité à la somme de Riemann littérale et à l’espérance sous la vraie loi
  source. Le théorème final est le fonctionnel de Laplace de
  \(\operatorname{PPP}(\lambda\,dt)\).
- `PaperC.Model.InfiniteRademacher` construit la loi produit infinie des
  signes premiers et prouve le lemme 14.4 sans pont. Une queue constante
  forcerait tous les bits premiers assez tardifs à zéro, événement de mesure
  nulle puisque ses cylindres de longueur \(N\) ont masse \(2^{-N}\).
  `InfiniteCylinderTransfer` prouve que toute projection finie est
  exactement la loi uniforme antérieure et que les valeurs multiplicatives
  coïncident sur les entiers couverts par le cutoff.
- `PaperC.Probability.InfiniteExactLengthProbabilityTransfer` spécialise
  cette image-loi aux événements de longueur exacte. Il prouve leur
  mesurabilité, les identifie à la préimage de l’événement fini lorsque le
  cutoff couvre \(x+q-1\), puis transforme exactement leur mesure infinie en
  probabilité uniforme rationnelle. La même identité est établie pour la
  double somme entière des starts retirés du lemme 14.7.
- `ExactLengthDecomposition` et
  `InfiniteExactLengthDecomposition` donnent presque sûrement, pour tout
  \(x\ge2\) et \(L\ge1\), un unique excès \(e\) sur l’événement de start.
  La forme cardinale vaut \(1\) sur ce dernier et \(0\) hors de celui-ci.
  Ils prouvent aussi \(e>E\Rightarrow J_{x,L+E+1}=1\), l’inclusion utilisée
  dans la dé-troncation des marques.
- `PaperC.Probability.MixedLengthAffine` certifie le lemme 14.5 dans le
  cylindre fini. Les événements de longueurs exactes \(q_e=L+e+1\) et
  \(q_f=L+f+1\) sont une unique fibre affine mixte, dont la probabilité vaut
  exactement
  \(2^{-q_e-q_f}\eta_{e,f}2^{\rho_{e,f}}\). Lorsque \(e,f\le E\),
  l’extension par zéro des coefficients de lignes injecte l’espace des
  relations mixtes dans celui des deux systèmes de longueur
  \(Q=L+E+1\), et Lean en déduit \(\rho_{e,f}\le\rho_Q\), sans pont.
- `PaperC.Probability.ExactLengthConditionalRank` formalise le noyau fini du
  lemme 14.7 après fixation des petits premiers. Les systèmes exacts sur
  `LargeSample` satisfont les identités \(\eta2^\rho/2^m\). Une réalisation
  des lignes par les arêtes, les pivots privés et le contrôle de l’espace
  cyclique donnent la marginale exacte \(2^{-q}\) dans le cas forêt et,
  lorsque le nombre cyclomatique local est au plus un,
  \[
    \mathbb P(K_{x,q}K_{y,r}=1\mid\mathcal F_Y)
      \le 2^{1-q-r}.
  \]
  L’instanciation arithmétique simultanée de ces hypothèses structurales est
  effectuée en aval par les modules Stein--Chen marqués, sans pont ajouté.
- `PaperC.Probability.ExactLengthBadStartMass` et
  `PaperC.Asymptotics.ExactLengthBadStartMassCritical` ferment le lemme
  14.7. La masse retirée est séparée entre supports déjà défectifs et
  systèmes de rang plein, sommée sur \(0\le e\le E\), puis normalisée à la
  longueur commune \(Q=L+E+1\). Le compte direct sur les sommets non-racines
  coûte un facteur \(2\) par rapport à la constante affichée dans le papier,
  sans changer la conclusion uniforme \(o_{C,E}(1)\).
  `lemma_fourteen_seven_finiteCylinder` est l’étape intermédiaire sur les
  probabilités rationnelles du cylindre ; `lemma_fourteen_seven` remplace
  exactement chaque terme par
  \(\mathbb P_\infty(K_{x,e}=1)\) et porte donc sur la loi infinie source.
- `PaperC.Probability.MarkedLocalGeometry` prouve directement que deux
  marques distinctes au même start et deux starts strictement chevauchants
  ont masse jointe nulle. Les intersections de support aux offsets
  \(L+e\) et \(L+e+1\) sont calculées exactement, préparant les contributions
  locales de Stein--Chen.
- `MarkedConditionalDependencyGraph`, `TwoStartLocalRank`,
  `MarkedSteinChenTerms` et `MarkedSteinChenSplitBound` ferment le calcul
  marqué. Les paires locales sont injectées dans une population
  \(O_E(N(L+E))\) et leur rang conjoint est borné par \(E+1\). Les paires
  séparées sont injectées dans les arêtes communes et leur défaut de rang
  est dominé par la masse homogène à \(Q=L+E+1\).
  `MarkedSteinChenCritical` transporte les bornes canoniques \(κ\) et obtient
  \(b_1,b_2=o_{C,E}(1)\) sans pont interne.
- `MarkedLaplaceFiniteClosure` compare exactement le fonctionnel complet au
  fonctionnel retenu par la masse du lemme 14.7 et contrôle la correction du
  paramètre. `MarkedLaplaceCritical` combine ces estimations aux limites de
  Riemann pour chaque cutoff fixé.
  `PaperC.Probability.FullMarkedLaplaceTransfer` définit séparément la
  fonctionnelle source littéralement complète, dont la somme intérieure
  parcourt tous les excès \(e\in\mathbb N_0\), et prouve qu’un test nul
  au-dessus de \(E\) donne exactement la fonctionnelle tronquée, point par
  point et après intégration. `MarkedDetruncationCritical` établit ensuite
  \[
    \limsup_N\mathbb P(\text{une marque}>E)
      \le\lambda2^{-(E+1)}
  \]
  et la tension uniforme quand \(E\to\infty\). Enfin
  `CorollaryFourteenEightMaximum` prouve
  \(\mathbb P(M_{N,L}\le m)\to
  \exp(-\lambda2^{-(m+1)})\) par la route canonique.
- `PrimeEncodedCountVector`, `PrimeEncodedCountLaplace`,
  `PoissonVectorMass` et `DirichletAtomConvergence` ferment l’autre partie
  du corollaire 14.8. Le codage par puissances des premiers est injectif ;
  les transformées inverses de la loi source sont exactement les
  fonctionnelles marquées aux tests \(s\log p_e\), celles de la cible sont
  le produit des transformées de Poisson, et l’inversion de Dirichlet donne
  la convergence de chaque atome du vecteur. L’endpoint canonique ne prend
  que AGG, Evertse--Silverman, Halter--Koch et Nicolas--Robin.
- `PaperC.Asymptotics.SectionFourteenClosure` fournit les deux endpoints
  publics `theorem_one_two_ii_laplace` et
  `theorem_one_two_iii_laplace_and_tightness`. Le second quantifie sur une
  structure de test continu positif munie de son témoin de support fini en
  marques, porte littéralement sur `infiniteFullMarkedLaplaceExpectation`,
  utilise l’égalité complète/tronquée de `FullMarkedLaplaceTransfer`,
  identifie la somme finie de la cible à la série complète sur
  \(\mathbb N_0\), puis associe la convergence de Laplace à la tension
  uniforme.
- `PaperC.Arithmetic.LowZonePrimePivots` et
  `PaperC.Asymptotics.LowZoneCritical` certifient le noyau fini du lemme
  15.1 : supports des premiers intermédiaires, indépendance linéaire, rang,
  identité
  \(r(x)=\pi(L)-\pi(\sqrt{x+L})\) et borne sommée. La conclusion \(o(1)\)
  ne demande plus de pont interne : Lean déduit le gap entier de
  \(x\le L^{2-\varepsilon}\) et établit lui-même la décroissance de
  l’enveloppe. Le seul pont `external` est désormais l’énoncé source
  \(\pi(t)\log t/t\to1\) du théorème des nombres premiers ; Lean en dérive
  la minoration uniforme
  \(3\log_2L\le\pi(L)-\pi(\sqrt{x+L})\) dans toute la zone du manuscrit.
- `PaperC.Arithmetic.LaishramShoreyInput`,
  `PolynomialZoneLargePrimes` et
  `PaperC.Asymptotics.PolynomialZoneCritical`, puis
  `PaperC.Asymptotics.PolynomialZoneSum`, ferment conditionnellement le
  lemme 15.2. Le corollaire 1 de Laishram–Shorey est un pont `external`
  transcrit avec son minimum et sa correction \(\delta(B)\) exacts. Lean
  retire les premiers \(\le B\), attache chaque premier restant à un unique
  sommet, écarte le sur-ensemble des premiers dont le carré divise un sommet
  — de cardinal au plus trois — et borne par deux le nombre de grands
  premiers simples par sommet. Il obtient ainsi le minorant fini exact des
  sommets non \(B\)-défectueux, le spécialise à
  \(B=L+1,\ L+2<x\le2L^2\), puis le transporte dans la borne de probabilité
  (15.1). Le PNT source donne aussi formellement le minorant de rang
  \(c_3B/\log B\) avec \(c_3=1/32\). Lean somme ensuite toutes les
  probabilités de la bande littérale \(L+2<x\le2L^2\) et prouve que cette
  masse tend vers zéro sous les deux ponts externes LS04 et PNT.
- `PaperC.Arithmetic.SquarefreeSmoothCount`,
  `PaperC.Asymptotics.SquarefreeSmoothCritical`,
  `PaperC.Asymptotics.HighZoneTwoDefects` et
  `PaperC.Asymptotics.LemmaFifteenThree` ferment conditionnellement le lemme
  15.3. Les noyaux carrés-libres \(B\)-friables sont injectés dans les
  sous-ensembles des premiers \(\le B\), d'où le majorant exact
  \(2^{\pi(B)}\), puis son échelle \(\exp(O(B/\log B))\) sous PNT. Lean
  assemble aussi le compte fini sur deux noyaux et deux offsets, construit
  les noyaux canoniques des sommets défectueux, exclut le cas de deux noyaux
  égaux dans la zone haute et couvre effectivement chaque fenêtre à deux
  défauts par l'union finie correspondante. Sous l’interface de Pell,
  désormais déchargée depuis ses deux entrées de littérature,
  le cardinal est borné par
  \[
    \#\mathcal D_B(3N)^2 B^2
      \exp\!\bigl(c\log(3N)/\log\log(3N)\bigr).
  \]
  Lean combine ensuite ces facteurs et compare uniformément
  \(\log(3N)/\log\log(3N)\) à l'échelle critique du paramètre supérieur
  \(M\). Il obtient exactement, avec une constante et un seuil indépendants
  du sous-bloc,
  \[
    \#\{x\in[N,2N):m_x\ge2\}
      \le \exp(KL/\log L),
    \qquad 2L^2\le N\le M,
  \]
  lorsque \(\lvert L-\log_2M\rvert\le C\). Les seuls ponts enregistrés sont
  PNT et les entrées de littérature du Pell généralisé (`external`).
- `PaperC.Arithmetic.BalasubramanianShoreyInput` enregistre le théorème 1 de
  Balasubramanian–Shorey comme pont `external`, avec les équations, les
  conditions de densité et la source primaire. Le module
  `BalasubramanianShoreyMaximum` prouve ensuite la décomposition canonique du
  produit des sommets défectueux, la friabilité du facteur restant et la
  conclusion littérale du lemme 15.4 :
  \[
    m_x\le B-g_B,\qquad g_B=B-\mu_B(\theta_0),
  \]
  pour \(B\) assez grand et \(x>B^2+2\), sous ce pont externe.
- `PaperC.Asymptotics.PropositionFifteenFive`,
  `PropositionFifteenFiveDecay`, `PropositionFifteenFiveClosure` et
  `PropositionFifteenFivePartition` ferment conditionnellement la
  proposition 15.5. Lean définit la masse
  littérale des starts \(2\le x<M/2^{j_0}\), couvre la zone
  \(x\le2L^2\) par les lemmes 15.1–15.2, insère simultanément les lemmes
  15.3–15.4 dans chaque bloc supérieur et prouve
  \[
    L\,e^{KL/\log L}\,2^{1-g_L}\longrightarrow0.
  \]
  La somme géométrique finie donne explicitement \(O(2^{-j_0})\), et le
  prédicat `DeepTruncationDoubleLimit` encode l'ordre
  \(j_0\to\infty\), puis \(M\to\infty\). La partition finie part de
  \(2L^2+1\), couvre exactement la zone haute par des blocs adjacents jusqu'au
  cutoff \(M/2^{j_0}\), traite le dernier bloc par son enveloppe entière et
  utilise au plus \(2L\) blocs. Le théorème public
  `PropositionFifteenFivePartition.proposition_fifteen_five` assemble ainsi
  la borne globale \(O_C(2^{-j_0})+o_M(1)\) et la double limite exacte, sous
  PNT, Laishram--Shorey et Balasubramanian--Shorey (`external`) et le Pell
  généralisé (`internal`), sans hypothèse de partition résiduelle.
- `PaperC.Combinatorics.BoundedRatioGeometry` et
  `PaperC.Asymptotics.BoundedRatioRationalMass` certifient le site nouveau
  du lemme 17.5. Pour \(U(N,M)=[N,M)\), Lean prouve le cardinal exact de
  l’intervalle et des majorants de classes et de canaux, sépare le canal
  volumique \(q=2\) des hauteurs \(q\ge3\), puis obtient la borne uniforme
  \(16(\kappa_0+1)(L+1)^4N2^{\lfloor L/2\rfloor}\). Sa conversion
  asymptotique borne sans pont la masse systématique par
  \(N^{3/2+o_{C,\kappa_0}(1)}=o_{C,\kappa_0}(N^2)\). La somme purement
  géométrique du lemme 17.6 est inchangée et sa borne linéaire
  sous-polynomiale déjà certifiée est réexportée.
- `PaperC.Combinatorics.BoundedRatioRelationalHosts`,
  `BoundedRatioResidualMasses`,
  `PaperC.Asymptotics.BoundedRatioRelationalHostsCritical`,
  `BoundedRatioCorrectedDefectEnvelope` et `BoundedRatioSectorClosure`
  fournissent le socle commun des secteurs 17.14–17.16. Le compte d’hôtes
  est effectué directement sur \([N,M)\), au cutoff exact \(M+L\), sans
  couverture dyadique. Les masses linéaire et quadratique sont reliées par
  Cauchy–Schwarz, tandis que les maxima uniformes de défaut corrigé et les
  enveloppes indépendantes de \(M\) sont transportés dans la fenêtre
  critique.
- `PaperC.Asymptotics.BoundedRatioSmallProductSector`,
  `BoundedRatioSmallHeightSector`,
  `BoundedRatioShallowCoreSigmaCritical` et
  `BoundedRatioShallowCoreSector` ferment respectivement les lemmes
  17.14–17.16. Les deux premiers secteurs donnent
  \(Q_{\rm res}\le N^{2+o(1)}\) et
  \(R_{\rm res}\le N^{7/4+o(1)}\). Le troisième donne
  \(Q_{\rm res}\le N^{19/8+o(1)}\) et
  \(R_{\rm res}\le N^{31/16+o(1)}\). Les trois petits-oh quadratiques sont
  des théorèmes Lean sans hypothèse de pont.
- `PaperC.Asymptotics.PropositionSixteenOne` définit la quantité littérale
  \(R_{2,\kappa}(N,L)\), prouve les identités de poids et construit, pour
  toute famille terminale fournie, les sept fibres ordonnées de la
  partition 17.31. Le module `BoundedRatioSectorAligned` transporte
  l’exclusion alignée au seul minorant commun \(N\), ce qui ferme sans pont
  l’instance \(\alpha=3/16\) du lemme 17.17, même à travers deux sous-blocs.
  `PropositionSixteenOneCore` sépare ce noyau du wrapper public afin d’éviter
  les cycles d’import. Le théorème générique assemble la proposition 16.1
  sous les trois interfaces `internal` des secteurs profonds (5)–(7).
  Le théorème canonique construit désormais les secteurs (5) et (6) depuis
  Evertse--Silverman et Pell, choisit lui-même le seuil terminal de (6), puis
  construit (7) depuis Pell et le théorème Lean source-exact de 9.10. Il ne
  prend donc plus aucune interface sectorielle de la section 17 ni hypothèse
  arithmétique de 9.10.
- `PaperC.Combinatorics.BoundedRatioCanonicalTerminalPopulation`,
  `BoundedRatioIntrinsicTerminalPopulation`,
  `PaperC.Asymptotics.BoundedRatioComponentNormalization`,
  `BoundedRatioComponentHosts`, `BoundedRatioTwoDefectStarts`,
  `BoundedRatioDistinctKernelTwoDefects`, `BoundedRatioManyDefectsReduction`,
  `BoundedRatioTerminalClosure` et `BoundedRatioTerminalFibers` fixent la
  population terminale, normalisent les composantes et isolent les
  invariants finis des secteurs 17.26–17.30.
- `PaperC.Asymptotics.BoundedRatioManyDefectsFibers` couvre les hôtes actifs
  littéraux par les fibres à base de fenêtre contenant deux défauts et forme
  fixée. `BoundedRatioManyDefectsFixedFibers` désintègre ensuite ces fibres
  par coefficient carré-libre : degré un fermé, degré deux réduit à Pell ou
  aux diviseurs signés, degré au moins trois réduit à Evertse--Silverman,
  avec hauteurs polynomiales automatiques.
  `BoundedRatioManyDefectsDegreeTwoSum` et
  `BoundedRatioManyDefectsEvertseSum` ferment les deux sommes
  subpolynomiales explicites ; le premier s’appuie notamment sur les bornes
  factorielles de `PrimeFactorsFactorialBound`.
  `BoundedRatioManyDefectsRealFibers`,
  `BoundedRatioManyDefectsDegreeAssembly` et
  `BoundedRatioManyDefectsAssembly` agrègent ensuite les degrés, les bases et
  les formes et ferment intégralement 17.26 sous les seuls ponts ES et Pell.
- `PaperC.Asymptotics.BoundedRatioNonterminalClosure` ferme le calcul des
  poids de 17.28. `BoundedRatioNonterminalCardinality` remplace le critère
  global laissé en v033 par la dichotomie source exacte et ferme les deux
  branches sous les comptes directs d’hôtes de tailles dix et deux.
  `BoundedRatioNonterminalHostCounts` et
  `BoundedRatioNonterminalRealHosts` désintègrent exactement les formes
  selon la branche mobile ou deux-singletons.
  `BoundedRatioTwoSingletonHosts` prouve l’injection arithmétique, la somme
  harmonique et le produit eulérien ; `BoundedRatioTwoSingletonCritical`
  absorbe le facteur global sûr \(9B^4\) et fournit
  \(N\exp(C_{\rm term}\sqrt B/\log B)\).
  `BoundedRatioNonterminalMobileAssembly` construit la branche modérée sous
  ES et Pell, et `BoundedRatioNonterminalAssembly` choisit
  \(K=(2C_{\rm term}+1)/\log2\) pour fermer intégralement 17.28.
- `PaperC.Asymptotics.BoundedRatioTerminalPartnerClosure` construit les
  fibres de partenaires de rang. `BoundedRatioTerminalSummation` en somme
  uniformément les premiers starts sous Pell, prouve les exposants
  \(3/4\) et \(7/4\), puis transporte exactement la conclusion vers la
  population intrinsèque par le théorème non aligné de 9.10, sans prémisse
  fournie. Ce dernier secteur n’est donc plus une dette propre de l’API
  canonique.
- `PaperC.Asymptotics.BoundedRatioSteinChen`,
  `BoundedRatioBadStarts`, `BoundedRatioWeightedDefect` et
  `BoundedRatioSteinChenRates` construisent les bons et mauvais départs de
  \([N,M)\), leur graphe conditionnel exact et leur cylindre uniforme.
  Lean prouve la marginale \(2^{-L}\), le paramètre conditionnel et sa
  correction exacte, puis les bornes uniformes
  \(\#D_Y=N^{1/2+o_{C,\kappa_0}(1)}\) et
  \(\sum_{x\in D_Y}\mathbb P(J_x)=o_{C,\kappa_0}(1)\). Il établit aussi
  \(b_1=o_{C,\kappa_0}(1)\), ainsi que sa spécialisation sur
  \([M/2^j,M)\) pour tout \(j\) fixé.
- `PaperC.Probability.FiniteCylinderCountTransport`,
  `PaperC.Asymptotics.BoundedRatioSteinChenSecondTerm` et
  `BoundedRatioSteinChenSecondTermCritical` prouvent le transport exact des
  lois entre cutoffs, la loi totale finie, la partition
  chevauchement/contact/séparation du second terme et
  \(\mathbb E b_2=o_{C,\kappa_0}(1)\). La branche séparée est dominée par
  \(R_{2,\kappa}\), la branche de contact possède la marginale jointe exacte,
  et le comptage d’arêtes vérifie
  \(E_{Y,U}=o_{C,\kappa_0}(N^2)\).
- `PaperC.Asymptotics.BoundedRatioPoissonAssembly`,
  `BoundedRatioFixedJBadStarts`,
  `PaperC.Probability.BoundedRatioRetainedTransport` et
  `PaperC.Asymptotics.TheoremSixteenTwo` assemblent AGG, le mélange
  conditionnel, le couplage bon/complet, le déplacement du paramètre, la
  moyenne et l’arrondi exact du bord \(M/2^j\). Les lemmes de transport
  nécessaires sont intégrés aussi dans `TheoremSixteenTwo` afin d’éviter un
  cycle d’import. Ils ferment sans pont interne supplémentaire les lemmes
  17.34–17.37 et le raccord au compte retenu.
- `PaperC.Asymptotics.TheoremSixteenTwo` construit sur un même cylindre les
  comptes global et retenu, leurs lois, leurs espérances et leurs paramètres
  de Poisson. Les estimations de couplage, le triangle TV, le recentrage,
  l’ordre des limites, l’équivalent de \(\Lambda_M\) et la probabilité de
  vide sont prouvés dans Lean. La compatibilité de marginale entre le
  cylindre global et chaque cylindre local est maintenant obtenue par une
  décomposition en produit des coordonnées premières, sans hypothèse. Le
  théorème public assemble directement la proposition 15.5 et la proposition
  16.1 quantifiée pour tout \(C'>0\) et tout \(\kappa_0\ge2\), avec une
  famille terminale autorisée à dépendre de ces paramètres ; l’estimation
  d’arêtes est elle aussi fournie pour tout \(C'>0\). L’assemblage générique
  direct expose les trois interfaces sectorielles `discharged`; les trois
  adaptateurs intermédiaires qui permettaient de les fournir par étapes sont
  supprimés en v041. L’API canonique construit les trois secteurs profonds :
  elle n’expose plus ni \(K\), ni famille terminale, ni hypothèse de la
  section 17. Seuls AGG, PNT, Laishram--Shorey,
  Balasubramanian--Shorey, Evertse--Silverman, Halter--Koch et
  Nicolas--Robin restent visibles.
  L’interface arithmétique de 9.10 et l’interface agrégée fixe-ratio ont
  disparu de ce chemin canonique.
- `PaperC.LinearAlgebra.PrivatePivots` et
  `PaperC.Probability.ConditionalStartProbability` certifient le lemme 13.1
  et le corollaire 13.2 dans le cylindre fini. Lean scinde exactement les
  coordonnées \(p\le Y\) et \(p>Y\), traduit le système après fixation
  arbitraire des petits premiers, puis utilise les pivots privés pour prouver
  la surjectivité de la partie grande hors \(D_Y\). Chaque fibre conditionnée
  vérifie
  \[
  \#\mathrm{solutions}\,2^L=\#\mathrm{affectations\ grandes},
  \]
  donc possède exactement la probabilité \(2^{-L}\). Cette égalité représente
  le conditionnement par la loi uniforme sur le cylindre restant, sans
  recourir à une API mesure-théorique.
- `PaperC.Combinatorics.GraphCycleRank` et
  `PaperC.Combinatorics.CycleSpaceDimension` : les dépendances entre vecteurs
  d'arêtes sont cycliques, la dimension de l'espace cyclique est majorée par
  la forme tronquée sûre \(|E|-(|V|-|C|)\), et la borne de rang du lemme 14.6
  en découle sous une hypothèse explicite de connexité aux racines.
- `PaperC.Coding.HammingBound` : volume exact des boules binaires,
  disjonction à distance minimale et borne de Hamming, y compris la forme de
  codimension utilisée en section 3 sous l'hypothèse réelle
  \(\dim C\ge n-r\), ainsi que les deux inégalités
  \(2^{n-r}\sum_{j\le t}\binom nj\le2^n\) et
  \(\sum_{j\le t}\binom nj\le2^r\) de (3.5).
- `PaperC.Coding.DefectCodeRank`, `DefectCodeRunge`,
  `DefectCodeRepresentation`, `DefectCodeDistance`,
  `DefectCodeProposition`, `RungeDefectApplication`,
  `HammingDefectBound` et `DefectCodeHamming` : rang--nullité exact de la
  matrice de défaut augmentée, poids pair, déduction de la couverture complète
  des coordonnées premières depuis \(f=s a^2\), produit carré, réindexation
  d'un mot non nul en \(d=2k\ge2\) données de Runge, distance minimale, raccord
  complet à (3.5) et borne finie
  \(m<2t\,2^{(r+1)/t+1}\). La comparaison terminale unique
  \((128(2t)R)^{4t}<U\) exclut tous les mots courts.
- `PaperC.Arithmetic.PrimesUpTo`, `PrimeCountBridge` et
  `ChebyshevPrimeCount` : énumération croissante canonique des premiers
  \(p\le H\), identification avec le finset arithmétique et borne élémentaire
  \(\lfloor\log_2H\rfloor\pi(H)\le7H\), sans théorème des nombres premiers.
- `PaperC.Arithmetic.DefectCounting`, `WeightedDefectCounting` et
  `DefectivePredicate` : équivalence, pour \(n>0\), entre \(K_H(n)=1\) et une
  représentation \(n=s a^2\) à support premier \(\le H\), puis comptages
  grossier et pondéré, dont
  \[
  \#\mathcal D_H^+(X)\le
  \sqrt X\prod_{p\le H}(1+p^{-1/2}).
  \]
- `PaperC.Analysis.RungeLogarithmicGrowth`, `ReciprocalSqrtSum`,
  `SmoothEulerProduct`, `DefectGlobalBound` et `WeightedDefectMass`, avec
  `PaperC.Coding.CanonicalDefectCode`, `IntervalDefectBound` et
  `PaperC.Combinatorics.IntervalDefectAggregation` : rayon entier par
  plancher logarithmique, branchement concret du code aux défauts d'un
  intervalle, produit eulérien \(\le e^{2\sqrt H}\), double comptage des
  intervalles et majorant fini uniforme assemblé précédant (3.4).
- `PaperC.Analysis.CriticalWindowParameters`, `CriticalWindowScale`,
  `DefectPointwiseRate`, `CriticalWeightedDefect` et
  `CriticalPointwiseIntervals` : fermeture complète de la proposition 3.2.
  Le rayon et son budget sont valides uniformément sous
  \(c_1\log N\le H\le c_2\log N\), tout intervalle admissible possède
  \(O_{c_1,c_2}(\log N/\log\log N)\) défauts, et la masse de (3.4) vérifie
  la formulation quantifiée de \(N^{1/2+o(1)}\).
- `PaperC.Asymptotics.ExpSqrtLog`, `CappedRadiusDyadic`, `HalfPower` et
  `LinearPower` :
  enveloppes uniformes pour \(e^{C\sqrt{\log N}}\), \(H+1\), le facteur
  dyadique de Hamming et leurs produits ; définitions kernel-checkées de
  \(N^{1/2+o(1)}\), \(N^{-1/2+o(1)}\) et \(N^{1+o(1)}\).
- `PaperC.Combinatorics.RungeCoefficients` et
  `PaperC.Analysis.RungePowerSeries` : développement binomial formel de
  \(\prod_\nu(1+\gamma_\nu X)^{1/2}\), identification exacte de son
  coefficient \(c_m\) à la somme sur les compositions faibles, intégralité
  de \(2^dc_m\) pour \(2m\le d\), majorant
  \(\lvert c_m\rvert\le(8R)^d\) dans la plage utile, et identité formelle
  \(F(X)^2=\prod_\nu(1+\gamma_\nu X)\).
- Les modules `RungeAnalyticProduct`, `RungeTailEstimate`, `RungeScaling`,
  `RungeEstimate`, `RungeTruncationBounds`, `RungeQPolynomial`,
  `RungeEquality`, `RungeNonEquality` et `RungeBound`, avec les modules
  précédents de coefficients, traduction et séparation dyadique, certifient
  **entièrement le lemme 3.1**. Lean vérifie la convergence du produit de
  séries, la branche positive, (3.3), les deux branches dyadique et
  polynomiale, \(\deg Q\le k-1\), la hauteur de \(Q\), puis
  \[
  U\le(128\,dR)^{2d}\qquad(d=2k\ge2).
  \]
  La constante absolue existentielle du manuscrit est donc instanciée par
  \(C_0=128\).
- `PaperC.Runs.Starts` : définition additive exacte d'un start et
  incompatibilité de deux starts qui se chevauchent
  (lemme 3.4(i)).
- `PaperC.Affine.TouchingSystem`, `TouchingDefectRank`,
  `PaperC.Combinatorics.TouchingPairs`, `PaperC.Analysis.TouchingMass`,
  `TouchingWindow` et `CriticalTouchingPairs` : système affine de deux starts
  à distance \(L\), frontière injective de leur arbre joint de \(2L\) arêtes,
  borne du défaut de rang par les défauts de \([x,x+2L]\), comptage des deux
  orientations et preuve complète du lemme 3.4(ii) sous
  \(\lvert L-\log_2N\rvert\le C\) :
  \[
  \sum_{\substack{x,y\in I_N\\|x-y|=L}}
    (2^{\rho(x,y)}-1)\le N^{1+o_C(1)}
  \]
  au sens uniforme quantifié.
- `PaperC.Model.FiniteRademacher` : modèle fini cylindrique de la fonction
  complètement multiplicative aléatoire et variable de comptage dyadique.
- `PaperC.Affine.StartSystem` : identification du start avec le système affine
  de la section 2.
- `PaperC.Probability.StartProbability` : raccord exact entre la probabilité
  cylindrique d'un start et le comptage de sa fibre affine.
- `PaperC.Probability.TouchingProbability` : probabilité cylindrique exacte
  de deux starts touchants, normalisation
  \(\eta2^\rho/2^{2L}\) et borne absolue par
  \((2^m-1)/2^{2L}\) sous \(\rho\le m\).
- `PaperC.Probability.FactorialMoment` et
  `PaperC.Probability.FiniteExpectation` : identité algébrique du second
  moment factoriel, puis preuve exacte de
  \(\mathbb E Z_{N,L}=\sum_x\mathbb P(J_{x,L})\) dans le cylindre fini.
- `PaperC.Affine.StartDefectRank`,
  `PaperC.Probability.DefectFirstMoment`, `CriticalFirstMoment` et
  `CriticalRunWindow` : injection des relations du start-tree dans les
  sommets défectueux, formule finie du premier moment, puis preuve du
  corollaire 3.3 sous sa fenêtre littérale
  \(\lvert L-\log_2N\rvert\le C\), avec erreur
  \(N^{-1/2+o_C(1)}\).
- `PaperC.Probability.FinitePMF` : noyau fini de variation totale.
- `PaperC.Asymptotics.Uniform` : quantificateurs explicites pour les notations
  asymptotiques uniformes.
- `PaperC.Affine.TwoStartSystem`,
  `PaperC.Affine.RelationalPrimeAssignment`,
  `PaperC.Arithmetic.LargeOddKernel`,
  `PaperC.Combinatorics.LargeKernelAssignments` et
  `PaperC.Combinatorics.RelationalHosts` : système affine de deux starts,
  sélection canonique d'une occurrence non nulle, affectation unique de
  chaque premier \(p>L+1\) de valuation impaire à une occurrence du bloc
  opposé, puis regroupement CRT des starts par affectation. Lean obtient
  exactement
  \[
  H_2(N,L)\le
  8(L+1)N\sum_{1\le n\le3N}
  \frac{(L+1)^{\omega(K_{L+1}(n))}}{K_{L+1}(n)}.
  \]
- `PaperC.Arithmetic.LargeKernelWeightedCounting`,
  `PaperC.Analysis.ReciprocalThreeHalvesTail`,
  `PaperC.Analysis.LargeEulerProduct`,
  `PaperC.Analysis.RelationalHostBound` et
  `PaperC.Asymptotics.ThreeHalvesPower`,
  `PaperC.Asymptotics.RelationalHostsThreeHalves` : décomposition canonique
  \(n=a^2ur\), majoration des deux produits eulériens sans théorème des
  nombres premiers, et fermeture de la borne finie
  \[
  H_2(N,L)\le
  8(L+1)N\sqrt{3N}\,e^{4\sqrt{L+1}}.
  \]
  Sous \(L+1\le C\log N\), ce majorant donne la formulation uniforme
  quantifiée de \(H_2(N,L)\le N^{3/2+o_C(1)}\), puis Lean la transporte à
  la fenêtre littérale \(\lvert L-\log_2N\rvert\le C\), ce qui certifie le
  lemme 4.2.
- `PaperC.Analysis.RelationalInterpolation` : Cauchy--Schwarz fini sur un
  sous-ensemble quelconque des hôtes relationnels, avec majorants séparés
  pour leur cardinal et la somme des carrés. Le calcul d'exposants de (4.3)
  est aussi vérifié explicitement :
  \(N^{3/2+\varepsilon}\) et
  \(N^{5/2-\delta+\varepsilon}\) donnent
  \(N^{2-\delta/2+\varepsilon}\). Sa version éventuelle uniforme certifie le
  lemme 4.3.

La table détaillée entre le manuscrit et Lean se trouve dans
[`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md). Le contrôle des
dépendances logiques est exécuté par
[`AuditCheck.lean`](AuditCheck.lean), dont la liste exhaustive et stable est
également fournie dans
[`audit_manifest.json`](audit_manifest.json). Le compte rendu humain reste
consigné dans [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md).

`#print axioms` ne détecte pas les hypothèses ordinaires passées en
arguments. Ici, « inconditionnel » signifie uniquement « ne dépend d'aucun
pont enregistré ». Le registre distingue :

- `external` : résultat publié vérifiable contre sa source, comme
  Evertse--Silverman ;
- `internal` : argument provenant de la preuve du manuscrit, comme le Pell
  généralisé ou un raccord d'assemblage ;
- `open` : pont encore requis par au moins une API canonique concernée ;
- `discharged` : interface historique conservée et vérifiable, mais dont la
  conclusion a maintenant été reconstruite dans Lean à partir d’entrées
  plus amont.

`kind` décrit donc la provenance, tandis que seul `status: open` signale une
dette restante. L'inventaire, le statut et la propagation de chaque pont par
théorème figurent dans `audit_manifest.json` et `AXIOM_AUDIT.md`. Le
manifeste porte également l'empreinte du PDF cible et la transcription
sourcée de chaque énoncé.

## Pourquoi le modèle probabiliste est d'abord fini

Pour une fenêtre contenue dans \([1,M]\), tous les événements considérés ne
dépendent que des signes des nombres premiers \(p\le M\). Le dépôt travaille
donc d'abord sur l'espace fini

\[
\Omega_M=\{0,1\}^{\{p\le M:p\ {\rm premier}\}},
\]

muni de la loi uniforme. Cette représentation est extensionnellement la
restriction cylindrique du produit infini, mais évite de faire intervenir les
produits infinis et l'espérance conditionnelle avant qu'ils ne soient
nécessaires.

Le cutoff `dyadicCutoff N L = 2*N + L` couvre bien toutes les fenêtres dont le
début appartient à `dyadicBlock N`. La fonction générique
`startProbability N L x` reste définie hors de ce bloc, mais elle y désigne
alors seulement la probabilité dans ce cylindre tronqué; aucune identification
avec le modèle infini n'est revendiquée hors de la zone couverte.

## Compilation

Le projet fixe Lean `v4.19.0` et mathlib `v4.19.0`.
Le manifeste Mathlib est conservé sans modification depuis la v018.

```bash
lake exe cache get
lake build
lake env lean AuditCheck.lean
node scripts/verify_audit.mjs
```

La dernière commande constitue l'audit exhaustif : elle exécute un
`#print axioms` pour chaque théorème ou lemme public, ainsi que pour les deux
constructions publiques porteuses de preuves conservées de l'audit
historique. `verify_audit.mjs` rejoue cette commande, vérifie qu’une sortie
correspond à chaque cible du manifeste régénéré et refuse automatiquement
tout élément hors de la liste blanche fondationnelle. Le fichier généré et
le manifeste se vérifient avant publication par :

```bash
node scripts/generate_audit.mjs --check
```

L'audit d'axiomes ne détecte pas les hypothèses ordinaires. Leur inventaire
est le registre des ponts de `audit_manifest.json` et d'`AXIOM_AUDIT.md` :
chaque entrée porte `kind: external | internal` et
`status: open | discharged`, et chaque théorème public conditionnel est
marqué avec la liste exacte et la nature des ponts qu’il prend comme
prémisses directes. En v041, les interfaces de 9.10, 9.2, 17.26, 17.28,
17.30 et l’ancienne enveloppe Nicolas--Robin portent
`status: discharged`. `kind: internal` décrit une provenance et ne signifie
donc pas, à lui seul, qu’une dette reste ouverte. Les cinq interfaces
`internal` sont toutes `discharged`; les sept entrées `open` sont toutes
`external`. Le manifeste v041 recense 3 970 théorèmes et 5 lemmes publics,
3 977 cibles d’audit, 3 825 résultats inconditionnels et 150 conditionnels,
ainsi que 13 ponts — huit `external`, cinq `internal`, sept `open` et six
`discharged`. Ces comptes sont reproduits dans `REPRODUCIBILITY.md`.

Le parseur du générateur couvre aussi le format où `theorem` ou `lemma` est
seul sur une ligne et où le nom commence sur la suivante. Cette correction
réintègre six déclarations, dont trois historiques, que l’ancien parseur
n’inventoriait pas.

## Ce qui bloque encore la certification complète

Les résultats externes sont isolés des dettes internes. Huit interfaces
externes sont désormais enregistrées : sept restent ouvertes et l’ancienne
enveloppe Nicolas--Robin spécialisée est conservée comme interface
déchargée de compatibilité.

- Evertse–Silverman (lemme 9.1), dont l'interface conditionnelle exacte est
  formalisée ;
- Arratia–Goldstein–Gordon / Stein–Chen (théorème 13.7), désormais représenté
  par une interface finie exacte ;
- le théorème des nombres premiers, sous sa forme source
  \(\pi(t)\log t/t\to1\), utilisé dans le lemme 15.1 ;
- le corollaire 1 de Laishram–Shorey utilisé dans le lemme 15.2 ;
- le théorème 1 de Balasubramanian–Shorey utilisé dans le lemme 15.4.
- le corollaire quantitatif de la théorie des idéaux d’ordres quadratiques
  utilisé pour colorier une fibre de norme par au plus \(4\tau(|M|)^2\)
  idéaux principaux ;
- le théorème de Nicolas–Robin sur le nombre de diviseurs, sous la forme
  logarithmique directe utilisée par `PellDivisorEnvelope` ;
- l’ancienne spécialisation éventuelle aux paramètres polynomialement
  bornés de 9.2, désormais `discharged` par ce module.

Les cinq interfaces `internal` correspondent à Pell, 9.10, 17.26, 17.28 et
17.30 ; elles sont toutes `discharged` et conservées pour la traçabilité.
Les anciennes interfaces P9.9, P9.11, T10.1 et C11.3 ont été supprimées avec
leurs endpoints publics génériques. Il ne reste donc aucun pont
`internal/open`. La formule « inconditionnel modulo littérature » décrit
exactement la frontière des endpoints canoniques, constituée uniquement des
sept résultats externes encore ouverts.

Le lemme 17.26 assemble maintenant ses sommes de diviseurs signés et
d’Evertse--Silverman ; le lemme 17.28 assemble les comptes d’hôtes mobiles et
deux-singletons et choisit lui-même \(K\) ; le lemme 17.30 était déjà fermé
sous Pell et utilise désormais le théorème Lean de 9.10 sans hypothèse
supplémentaire. Les théorèmes canoniques 16.1 et 16.2 ne prennent donc aucun
pont interne. L’identité de marginale
entre deux cutoffs finis, les bornes de mauvais départs, \(b_1\), \(b_2\),
le mélange, le couplage, la moyenne et l’arrondi du bord sont également
déchargés. L’ancienne interface `BoundedRangePoissonApproximation` n’est plus
enregistrée. Le théorème 16.2 générique direct conserve les trois prémisses
sectorielles `discharged`, mais ses adaptateurs intermédiaires ont été
supprimés. Sa variante canonique principale ne reçoit plus ni seuil \(K\),
ni famille terminale, ni prémisse de la section 17.

Le lemme quantitatif de Runge, la proposition 3.2, le corollaire 3.3, les
deux parties du lemme 3.4, les lemmes 4.2--4.3, les lemmes 5.1--5.2 et 5.5,
la proposition 5.4, ainsi que les lemmes 6.1 et 6.4--6.5 sont maintenant
entièrement certifiés dans le modèle fini sous leurs hypothèses explicites.
La conclusion de classe carrée du lemme 6.2 et le lemme 6.3, y compris la
disjonction des paires d'occurrences et la distinction des composantes
associées aux unités distinctes, sont également certifiés. Cela comprend la
fermeture uniforme des seuils de la fenêtre critique, les quantificateurs
remplaçant \(O_{c_1,c_2}\), \(N^{1/2+o(1)}\) et
\(N^{-1/2+o_C(1)}\), ainsi que les rangs du start-tree et du double arbre
touchant. Les lemmes 7.1 et 7.2, ainsi que les propositions 7.3, 7.4 et 7.5, sont
maintenant certifiés dans leurs formulations finies effectives, avec des
constantes explicites. Pour la proposition 7.5, Lean conserve la population
littérale \(P^\#>N\), hors petite hauteur, avec
\(16c^\#\le3(L+1)\), puis prouve
\(Q_{\rm res}\le N^{19/8+o_C(1)}\) et
\(R_{\rm res}\le N^{31/16+o_C(1)}=o_C(N^2)\). La partition exacte des
secteurs 7.3--7.5 et du cœur profond restant est également certifiée.
Restent notamment la généralisation littérale de l'instance
\(\alpha=3/16\) du théorème 8.1 à un paramètre positif arbitraire. La preuve
interne de Pell est déchargée ; seules ses deux entrées de littérature
Halter--Koch et Nicolas--Robin restent explicites. Les anciennes routes
publiques arbitraires de 9.9–11.3 et du §12 ont été retirées en v041 ; leurs
noyaux finis restent dans les modules, tandis que la masse mère canonique est
fournie par les preuves \(κ\). Les lemmes 13.3–13.5, les termes du
lemme 13.8 et le raccord booléen complet à l’interface AGG sont maintenant
certifiés. La conclusion qualitative du corollaire 13.9 découle de l’endpoint
canonique quantitatif, plutôt que d’une seconde route publique legacy. Le
corollaire 13.10 assemble le terme d'arêtes au cutoff terminal, les termes
quantitatifs de Stein–Chen et le triangle de variation totale pour donner le
taux uniforme
\(O((\log\log N)^{-2})\). Cette conclusion est la forme quantitative
conditionnelle du théorème 1.1 dans le cylindre fini. Son entrée
canonique utilise AGG, Evertse--Silverman, Halter--Koch et l’inégalité
logarithmique Nicolas--Robin. Le
\(o_C(N^2)\) de 13.6 est certifié au cutoff littéral. La proposition 14.1
est fermée dans la fenêtre log-log du manuscrit et la proposition 14.2
canonique utilise désormais AGG et la masse mère quantitative \(κ\), sans
pont interne. Les identités de Laplace, leurs limites de Riemann, le calcul
Stein--Chen marqué et la dé-troncation du §14 sont assemblés. Le lemme 15.1 possède son noyau
fini complet et sa conclusion ne
dépend plus que du pont externe PNT : l’ancienne dette interne du gap a été
déchargée.

La version 7c contient désormais le corollaire 11.3, qui énonce explicitement
la version quantitative requise pour le taux du corollaire 13.10 :

\[
R_2(N,L)\ll_C N^2
\exp\!\left(-c_R\frac{\sqrt{\log N}}{\log\log N}\right),
\qquad c_R=c_R(A,C)>0.
\]

Le chaînon est donc présent dans le manuscrit. La v041 supprime l’ancienne
formalisation publique sectorielle de 11.3 et conserve la voie canonique :
elle construit la masse mère quantitative depuis les preuves \(κ\), puis
injecte cette unique estimation dans l’assemblage probabiliste de
`PaperC.Asymptotics.CorollaryThirteenTen`.

## Ordre recommandé pour la suite

1. Généraliser de l’encodage rationnel déjà disponible à l’énoncé littéral
   pour tout réel \(\alpha>0\) du théorème 8.1.
2. Si un endpoint autonome du théorème 1.4 est souhaité, raccorder le noyau
   fini du §12 directement à la masse mère canonique, sans réintroduire les
   anciennes interfaces génériques.
3. Si une API mathlib stable apparaît, transporter les caractérisations de
   Laplace déjà prouvées vers une formulation équivalente en convergence
   vague de mesures ponctuelles.
