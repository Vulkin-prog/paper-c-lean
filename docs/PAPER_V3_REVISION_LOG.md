# Registre des révisions proposées pour le papier et le compagnon — v3

Dernière mise à jour : 6 septembre 2026.

Ce registre rassemble les corrections, clarifications et améliorations suggérées par la formalisation. La version source examinée est la **v2.8.2 anglaise** du papier et de son compagnon technique. La « v3 » désigne ici la prochaine révision à préparer ; les PDF fournis n'ont pas été modifiés.

Les identifiants restent stables au fil des mises à jour. Une **correction confirmée** répond à un énoncé littéralement incorrect ou à une ambiguïté dont une lecture est réfutée. Une **suggestion** améliore l'exposition sans signaler d'erreur du texte actuel. Le statut « à intégrer » ne signifie pas que la modification est déjà acceptée par l'auteur ou appliquée au manuscrit.

L'identité exacte des deux PDF est conservée dans le [manifeste des sources](../PaperCV282/source_manifest.json). Les pages ci-dessous sont les pages imprimées du document concerné. La [liste des résultats formalisés](../PaperCV282/ENDPOINTS.md) distingue les preuves obtenues des obligations encore ouvertes.

## Tableau de suivi

| ID | Document et emplacement | Type | Statut |
|---|---|---|---|
| V3-C001 | Papier, p. 9, clause conditionnelle du corollaire 2.6 ; convention p. 8 | Correction confirmée de formulation | À intégrer dans le prochain brouillon ; PDF inchangé |
| V3-S001 | Papier, p. 25, proposition 3.26 et équation (3.24) | Suggestion d'explicitation | Proposition à examiner |
| V3-S002 | Papier, p. 9, preuve du corollaire 2.6 | Suggestion d'explicitation du modèle fini | Proposition à examiner |
| V3-S003 | Papier, p. 14–15, preuve de la proposition 3.7 après (3.11) | Suggestion de simplification de la preuve | Proposition à examiner |
| V3-S004 | Papier, p. 9, clause sommée du corollaire 2.6 | Suggestion d'explicitation de l'espérance et de l'uniformité | Proposition à examiner |
| V3-S005 | Papier, p. 17, proposition 3.12, secteur 1 ; définition p. 13 | Suggestion de simplification de preuve | Proposition à examiner |
| V3-S006 | Papier, p. 17–18, lemmes 3.13–3.14 ; section de formalisation p. 50 | Suggestion de précision sur les taux formalisés | Proposition à examiner |
| V3-S007 | Papier, p. 22–24, secteur 8 et proposition 3.25 ; p. 26, plafond de 3.27 | Suggestion de simplification de preuve démontrée | Proposition à examiner |
| V3-S008 | Papier, p. 27–28, théorème 4.1 et suppression masquée | Suggestion de renforcement local au masque | Proposition à examiner |
| V3-S009 | Papier, p. 29, théorème 4.3 ; compagnon B.3, p. 8–9 | Suggestion de preuve soft commune à toutes les intensités | Proposition à examiner |
| V3-S010 | Papier, p. 32, corollaire 5.3 et équation (5.8) | Suggestion de renforcement en une espérance exacte | Proposition à examiner |
| V3-S011 | Compagnon, p. 10–12, preuve directionnelle autour de (C.2)–(C.5) | Suggestion d'explicitation de l'entrée bibliographique | Proposition à examiner |

| V3-S012 | Papier p.40 ; compagnon D.1 p.15, formule locale de Poisson | Suggestion de reste effectif | Proposition à examiner |
| V3-S013 | Papier p.42, proposition7.3 ; compagnon E.5 p.20 | Suggestion de simplification par comptage global | Proposition à examiner |

**Compagnon technique : aucune correction confirmée à ce stade.** Les résultats finis déjà formalisés ne constituent pas une vérification intégrale de ses annexes. Les prochaines observations propres au compagnon seront ajoutées avec leur emplacement et leur justification ; aucune anomalie ne lui est attribuée par analogie avec le papier.

## V3-C001 — Exiger une valuation impaire, pas seulement un premier impair

**Document et emplacement.** Papier v2.8.2, p. 9, clause conditionnelle du corollaire 2.6. La convention pertinente figure p. 8, dans la définition du noyau des grands premiers et des entiers défectueux.

**Type.** Correction confirmée de formulation. La condition voulue est cohérente avec les définitions et la preuve ; sa lecture littérale plus faible est fausse.

**Constat et justification.** L'expression « odd prime divisor above `Y > B` » qualifie littéralement le nombre premier, alors que l'argument exige que **sa valuation dans le sommet soit impaire**. La présence d'un grand facteur premier à puissance paire ne fournit pas une coordonnée binaire privée non nulle.

Contre-exemple à la lecture littérale : prendre `B = 2`, `Y = 3`, `x = 26`, donc la fenêtre `{25, 26}`. Chaque entier possède un diviseur premier impair supérieur à 3 : respectivement 5 et 13. Mais `25 = 5²` impose `f(25) = +1` par complète multiplicativité. Tout mot commençant par `−1` a donc probabilité conditionnelle zéro, pour chaque affectation des signes des premiers au plus 3, au lieu de `2⁻² = 1/4`. Le sommet 25 ne satisfait pas l'hypothèse voulue : sa valuation en 5 est paire.

**Formulation anglaise proposée.**

> If, for every vertex n in V_x, there exists a prime p > Y, where Y > B, such that v_p(n) is odd, then P(I_{x,w} = 1 | F_Y) = p_B for every realization of F_Y.

On peut également écrire « every vertex satisfies `K_Y(n) ≠ 1` », en renvoyant à la définition p. 8. Cette modification concerne la clause conditionnelle, sans changer l'équation (2.6).

**Statut.** À intégrer dans le prochain brouillon ; proposition non encore appliquée aux PDF. Le contre-exemple est un argument arithmétique explicite documenté dans la note, sans revendication d'une déclaration Lean dédiée à `{25,26}`.

**Preuve et notes.** [Note détaillée](../PaperCV282/MANUSCRIPT_NOTES.md) ; [WindowValues.lean](../PaperCV282/WindowValues.lean), déclarations `private_prime_of_not_defective` et `corollary_two_six_conditioned`. Cette dernière utilise explicitement `¬HDefective Y n`. Le module [InfiniteConditionalWords.lean](../PaperCV282/InfiniteConditionalWords.lean) établit désormais cette loi dans le modèle infini, sur chaque atome de masse positive de la sigma-algèbre des premiers au plus `Y`, identifiée explicitement. La présentation par un noyau général ou une espérance conditionnelle abstraite reste distincte.

## V3-S001 — Rendre explicite le compteur d'hôtes sans parité

**Document et emplacement.** Papier v2.8.2, p. 25, proposition 3.26, preuve de (3.24) et terme `H^{val}_{2,δ}`.

**Type.** Suggestion d'explicitation, **sans erreur identifiée**. Le texte distingue déjà les relations complètes des relations soumises aux deux parités.

**Justification.** La formalisation fournit une équivalence linéaire entre les relations des deux systèmes de départ et le noyau des **deux sommes de coefficients séparées**, à l'intérieur de l'espace complet des relations de valeurs. Avec `B = L + 1`, la nullité complète dépasse celle des départs d'au plus deux. La correction `+3` doit compter les paires ayant une relation complète non nulle, y compris celles dont le système de départ n'a aucune relation non nulle.

Les hôtes correspondants sont exactement les paires admettant un **sous-ensemble non vide des occurrences de sommets dont le produit est un carré**, sans condition de cardinalité paire dans l'un ou l'autre bloc. La positivité des valeurs et un cutoff contenant tous les sommets sont explicités dans l'identification avec le cylindre fini.

**Ajout anglais proposé après la définition du compteur.**

> Here the host count includes every separated ordered pair admitting a nonempty square-product subset of the full vertex occurrences. No even-cardinality condition is imposed in either block; a pair can contribute to this count even when its relative-sign kernel is zero.

**Statut.** Proposition à examiner. L'identification et l'inégalité finie (3.24) sont formalisées sous leurs hypothèses explicites. La borne dyadique est désormais complétée par la borne `M^(3/2+o(1))` sur tout masque de paires dans `[2,M]²`, puis sur les paires séparées du domaine macroscopique exact `[ceil(M^δ),M)`. Le théorème `FullIntervalHostAsymptotics.proposition_three_seven` établit conjointement la comparaison des compteurs de départs et de valeurs et la borne du second, avec cutoff `M+L` pour les relations de départ. Le seuil précède `L` et `δ`, sous `L+1 ≤ C log M` et `δ > 0`. Les inégalités d'hôtes de la proposition 3.7 sont ainsi acquises. Le raccord à rapport borné établit aussi la borne à l'échelle inférieure `N`, pour `N ≤ M ≤ κ N` avec `κ` naturel fixé et `L+1 ≤ C log N`, uniformément sur les masques dans `[2,M]²`. Il inclut la comparaison des compteurs sur les paires séparées de `[N,M)`. Le lot 9 a ensuite complété le profil brut du théorème 3.1 et sa combinaison en (3.25), comme indiqué ci-dessous.

Les masses pondérées macroscopiques `Rstart` et `Rval` sont désormais définies exactement sur ce même domaine et ce même cutoff. La masse de départs est identifiée à `R2κ` et hérite de la décomposition systématique/résiduelle du code canonique historique, pour tout paramètre naturel `A`. La partition successive des huit secteurs est maintenant définie et sa décomposition de masse est prouvée dans `ResidualSectorPartition` et `ResidualSectorMass`. L'identité seule ne fournit pas leurs estimations asymptotiques. Le coût positif de la comparaison est maintenant formalisé : `max(0,Rval−4Rstart) ≤ 3 Hval`, puis, pour tout entier `k > 0`, sa puissance `2k` est finalement au plus `M^(3k+1)`, uniformément sous `L+1 ≤ C log M` et `δ > 0`, avec seuil avant `L` et `δ`. Il s'agit d'une **majoration de la partie positive**, sans hypothèse de profil brut ; ces seuls lemmes intermédiaires ne donnent ni une erreur absolue, ni une égalité asymptotique, ni (3.25). Cette limite ne décrit pas la couverture globale obtenue au lot 9.

**Preuves.** [TwoWindowParity.lean](../PaperCV282/TwoWindowParity.lean), `startRelationEquivParityKernel` et `value_weight_le_four_start_weight_add_host` ; [ValueSquareRelations.lean](../PaperCV282/ValueSquareRelations.lean), `relationRho_ne_zero_iff_exists_nonempty_square_product` ; [TwoWindowSquareHosts.lean](../PaperCV282/TwoWindowSquareHosts.lean), `finite_equation_three_twenty_four_square_hosts` ; [FullHostComparison.lean](../PaperCV282/FullHostComparison.lean), `card_startRelationHosts_le_squareProductHosts` ; [FullIntervalHostAsymptotics.lean](../PaperCV282/FullIntervalHostAsymptotics.lean), `proposition_three_seven` ; [BoundedRatioFullHosts.lean](../PaperCV282/BoundedRatioFullHosts.lean).

**Preuves du coût positif.** [MacroscopicRelationProfile.lean](../PaperCV282/MacroscopicRelationProfile.lean), `macroscopicStartMassNat_cast_eq_R2kappa`, `macroscopicStartMassNat_cast_eq_systematic_add_residual` et `macroscopicValueMassNat_le_four_start_add_hosts` ; [MacroscopicValueCorrection.lean](../PaperCV282/MacroscopicValueCorrection.lean), `macroscopicValueExcess_cast_eq_max` et `prescribed_value_correction_uniform`.

**Avancement du profil rationnel.** Les trois bornes de la proposition 3.8 sont désormais formalisées séparément : masses réellement filtrées par hauteur canonique `q=2` et `q≥3`, et somme de géométries en base 2 sans translations. Les facteurs `Q_B^(1/2)` et `Q_B^(1/3)`, avec `Q_B=2^(L+1)`, restent explicites. Le raccord au canal canonique macroscopique pour `A=3` utilise un seuil dépendant de `δ>0` fixé, choisi avant la longueur et les départs ; les bornes numériques seules sont uniformes sur la borne inférieure de l'intervalle. La contribution rationnelle est complète. Le lot 8 définit également les huit secteurs et prouve leurs premières estimations ; l'état exact des secteurs profonds figure dans le registre des résultats. Le lot 9 complète le secteur 8 et les profils globaux brut, interpolé et plafonné, dans les domaines macroscopique, dyadique et à rapport borné. Il n'ajoute aucune correction de formulation. Voir [RationalHeightMass.lean](../PaperCV282/RationalHeightMass.lean), `boundedRationalMass_eq_height_masses` ; [RationalGeometryMass.lean](../PaperCV282/RationalGeometryMass.lean), `geometry_mem_sum_iff` et `geometryMass_le_poly_two_pow_half` ; [MacroscopicCanonicalCode.lean](../PaperCV282/MacroscopicCanonicalCode.lean), `canonical_rational_code_eq_of_nonzero_eventually` ; [RationalProfile.lean](../PaperCV282/RationalProfile.lean), `proposition_three_eight`.

## V3-S002 — Indiquer pourquoi un cylindre fini donne exactement la loi du mot

**Document et emplacement.** Papier v2.8.2, p. 9, preuve du corollaire 2.6 et interprétation probabiliste de la matrice de valeurs.

**Type.** Suggestion d'explicitation, **sans erreur identifiée**.

**Justification.** Pour une fenêtre de valeurs positives, tout cylindre contenant les premiers jusqu'au plus grand sommet représente exactement l'événement de mot du modèle infini. L'événement infini est l'image réciproque de l'événement fini, et les probabilités sont égales. Les signes des valeurs aux entiers restent ceux de la fonction complètement multiplicative, avec leurs dépendances arithmétiques ; seules les coordonnées premières sont indépendantes.

**Ajout anglais proposé.**

> For a fixed window of positive integers, choose a prime cutoff at least as large as its largest vertex. The word event depends only on these prime coordinates, so its probability in the infinite Rademacher product is exactly its probability on this finite cylinder.

**Statut.** Proposition à examiner. Le transfert inconditionnel et la borne ponctuelle infinie (2.6) sont formalisés. Le transfert conditionnel sur chaque atome des petits premiers est également formalisé dans [InfiniteConditionalWords.lean](../PaperCV282/InfiniteConditionalWords.lean). L'estimation sommée du premier moment est désormais formalisée pour les masques et dictionnaires dyadiques dans [WordFirstMomentAsymptotics.lean](../PaperCV282/WordFirstMomentAsymptotics.lean), avec la véritable espérance inconditionnelle du nombre d'occurrences et une uniformité explicitée en V3-S004. La présentation de la loi conditionnelle par une espérance conditionnelle abstraite reste distincte.

**Preuves.** [InfiniteWordTransfer.lean](../PaperCV282/InfiniteWordTransfer.lean), `infiniteWordEvent_eq_preimage`, `infiniteWordEvent_measure_eq_uniformSolutionProbability` et `corollary_two_six_pointwise_infinite`.

## V3-S003 — Une majoration élémentaire suffit pour l'étape de comptage des hôtes

**Document et emplacement.** Papier v2.8.2, p. 14–15, preuve de la proposition 3.7, majoration des deux produits eulériens après (3.11).

**Type.** Suggestion de simplification, **sans erreur identifiée**. La majoration du papier est plus fine ; il est possible d'utiliser une borne moins précise qui suffit à cette conclusion.

**Justification.** Pour `B ≥ 1`, les sommes sur les premiers se majorent ici par les sommes sur tous les entiers. Les deux produits sont chacun au plus `exp(2√B)`, ce qui donne

```text
∑_{1 ≤ n ≤ X} B^{ω(K_B(n))} / K_B(n) ≤ √X exp(4√B).
```

Dans une bande `B ≤ C log M`, le facteur `B exp(4√B)` est déjà `M^{o(1)}`. Pour cette étape du comptage des hôtes, il n'est donc pas nécessaire de gagner le facteur `1/log B` dans l'exposant, ni d'invoquer le théorème des nombres premiers pour obtenir ce gain. Cette observation ne supprime pas les utilisations des estimations sur les premiers dans les autres parties du papier.

**Formulation anglaise proposée.**

> For the host bound, the elementary majorant `√X exp(4√B)` for the weighted kernel sum already suffices. Indeed, when `B ≤ C log M`, the remaining factor `B exp(4√B)` is `M^{o(1)}`. The sharper prime-sum estimates are not needed for this step.

**Statut.** Proposition à examiner. La majoration de la somme pondérée et ses applications uniformes aux hôtes dyadiques, globaux et macroscopiques sont vérifiées en Lean sans hypothèse de littérature externe. La proposition 3.7 est désormais couverte par la comparaison des deux compteurs et la borne uniforme en puissance sur `[ceil(M^δ),M)`, avec seuil indépendant de `L` et de `δ`, sous `L+1 ≤ C log M` et `δ > 0`. Le gain plus fin dans les produits eulériens n'est donc pas nécessaire pour cette étape macroscopique. Le même majorant donne aussi le raccord à l'échelle `N` lorsque `N ≤ M ≤ κ N` avec `κ` naturel fixé et `L+1 ≤ C log N`, uniformément sur la borne supérieure de l'intervalle, la longueur et le masque. Cela ne prouve ni le profil brut du théorème 3.1, ni (3.25), ni le profil plafonné de la proposition 3.27.

La contribution rationnelle de la proposition 3.8 est maintenant traitée séparément par [RationalProfile.lean](../PaperCV282/RationalProfile.lean), avec ses deux filtres de hauteur et sa somme géométrique en base 2. Cette avancée ne change pas la portée de V3-S003 : la simplification proposée concerne seulement les produits eulériens de l'étape de comptage des hôtes, et ne remplace aucune estimation requise dans les secteurs résiduels.

**Preuves.** [RelationalHostBound.lean](../PaperC/Analysis/RelationalHostBound.lean), `sum_largeKernelWeight_le_sqrt_mul_exp` ; [FullHostAsymptotics.lean](../PaperCV282/FullHostAsymptotics.lean), `card_squareProductHosts_cast_le_exp_bound` et `card_squareProductHosts_uniformThreeHalves` ; [FullIntervalHostAsymptotics.lean](../PaperCV282/FullIntervalHostAsymptotics.lean), `card_squareProductHosts_cast_le_exp_bound`, `card_squareProductHosts_uniformThreeHalves_logarithmic` et `proposition_three_seven` ; [BoundedRatioFullHosts.lean](../PaperCV282/BoundedRatioFullHosts.lean). Le premier résultat est un lemme analytique historique réutilisé ; les raccords aux hôtes sans parité sont nouveaux.

## V3-S004 — Expliciter le premier moment et l'uniformité sur les masques et dictionnaires

**Document et emplacement.** Papier v2.8.2, p. 9, dernière clause du corollaire 2.6 : erreur du premier moment sommée sur une collection déterministe de mots distincts et un masque dans `I_N`.

**Type.** Suggestion d'explicitation, **sans erreur identifiée**.

**Justification.** La quantité considérée est l'espérance inconditionnelle, dans le modèle de Rademacher infini, du nombre total d'occurrences

```text
C_{s,W} = ∑_{x ∈ s} ∑_{w ∈ W} I_{x,w}.
```

Sa référence est `|s|·|W|·2⁻ᴮ`. La formalisation choisit le seuil en `N` avant la longueur `B`, le masque `s` et le dictionnaire `W`. Pour une bande fixée `0 < c₁ < c₂`, l'erreur est donc uniforme sur tous ces choix, même lorsque le masque, les mots et leur nombre varient avec `N` et `B`. Les dictionnaires et masques restent déterministes ; aucune indépendance entre occurrences n'est utilisée. Le cas du dictionnaire vide est inclus.

Le masque sélectionne les **départs** dans `I_N = [N,2N)`. Chaque occurrence conserve ses `B` sommets `x−1,…,x+B−2`, même si certains sont hors du masque ou du bloc des départs. Cette précision évite de remplacer l'événement de mot par un événement tronqué au bord.

**Formulation anglaise proposée.**

> Fix `0 < c₁ < c₂`. Uniformly for `c₁ log N ≤ B ≤ c₂ log N`, every deterministic start mask `s ⊆ I_N` and every dictionary `W ⊆ {±1}^B` of distinct words satisfy
>
> `E[∑_{x ∈ s} ∑_{w ∈ W} I_{x,w}] = |s| |W| 2⁻ᴮ + O_{c₁,c₂}(|W| 2⁻ᴮ N^{1/2+o(1)})`.
>
> The expectation is unconditional, and the error bound is uniform in `s` and `W`, which may vary with `N` and `B`. The mask restricts the start positions; each occurrence uses all `B` vertices `x−1,…,x+B−2`, without truncation at the boundary of the mask or of `I_N`.

**Statut.** Proposition à examiner. Le compte réel d'occurrences, son intégrabilité, l'identité d'espérance et la borne uniforme sommée sont formalisés sur les masques dyadiques. Le théorème n'impose ni condition de balance sur `N/2ᴮ`, ni hypothèse de bonnes fenêtres. Cette entrée n'étend pas la portée aux géométries macroscopiques ni au profil (3.25).

**Preuves.** [InfiniteWordFirstMoment.lean](../PaperCV282/InfiniteWordFirstMoment.lean), `wordOccurrenceCount`, `integrable_wordOccurrenceCount`, `integral_wordOccurrenceCount` et `abs_wordProbabilitySum_sub_baseline_le` ; [WordFirstMomentAsymptotics.lean](../PaperCV282/WordFirstMomentAsymptotics.lean), `corollary_two_six_summed_probability` et `corollary_two_six_summed_expectation`. Le dernier énoncé place explicitement le seuil avant `B`, `s` et `W`.

## V3-S005 — Simplifier le petit produit du secteur 1

**Document et emplacement.** Papier v2.8.2, p. 17, preuve de la proposition 3.12 pour le secteur 1 ; définition du produit canonique p. 13.

**Type.** Suggestion de simplification de preuve, **sans erreur identifiée**. Les moments croissants du papier ne sont pas remis en cause ; une majoration ponctuelle suffit pour ce profil.

**Justification.** Le certificat canonique a exactement `c#` premiers **distincts**, tous supérieurs à `B`. On a donc `(B+1)^c# ≤ P#`. Sous `P# ≤ M`, cela donne `c# log(B+1) ≤ log M`. Pour tout entier fixé `k`, dès que `2^k ≤ B+1`, on obtient `(2^c#)^k ≤ M`. La borne inférieure `betaMin log M ≤ B`, avec `betaMin > 0` fixé, implique ainsi `2^c# = M^{o(1)}` uniformément sur les certificats.

Avec la borne macroscopique `2^D# = M^{o(1)}` et `tau ≤ D# + c#`, on a `2^tau = M^{o(1)}`. Pour `sigma=0`, le poids résiduel est supporté sur les hôtes relationnels, dont le nombre est `M^{3/2+o(1)}`. Pour `sigma>0`, `2^sigma ≤ 2(2^sigma−1)` permet d'utiliser directement la masse rationnelle. La proposition 3.8 donne alors le profil annoncé `M^{o(1)}(M^{3/2}+M Q_B^{1/2})`, sans supposer `Q_B` comparable à `M` ni un rapport borné entre les départs.

**Formulation anglaise proposée.**

> In the small-product sector, the canonical certificate contains exactly `c#` distinct primes greater than `B`. Hence `(B+1)^c# ≤ P# ≤ M`, and `2^c# = M^{o(1)}` uniformly in the fixed logarithmic band. Together with `tau ≤ D# + c#`, this gives a pointwise subpolynomial residual factor. The branch `sigma=0` is bounded by the host count; for `sigma>0`, the inequality `2^sigma ≤ 2(2^sigma−1)` reduces the contribution to the rational mass. These two estimates yield the first profile in Proposition 3.12.

**Statut.** Proposition à examiner. La preuve est formalisée et a fait l'objet d'une relecture indépendante. La borne sur les moments croissants eux-mêmes n'est pas revendiquée par cette simplification.

**Preuves.** [SmallProductComponentBound.lean](../PaperCV282/SmallProductComponentBound.lean), `base_pow_componentCount_le_primeProduct` ; [MacroscopicSmallProductLoss.lean](../PaperCV282/MacroscopicSmallProductLoss.lean), `two_pow_pairTau_le_rpow_eventually` ; [SmallProductMass.lean](../PaperCV282/SmallProductMass.lean), `sectorMass_le_factor_hosts_add_rational` ; [MacroscopicSmallProductProfile.lean](../PaperCV282/MacroscopicSmallProductProfile.lean), `sector_one_mass_le_profile_eventually`.

## V3-S006 — Identifier la conséquence uniforme effectivement vérifiée pour Pell et les produits décalés

**Document et emplacement.** Papier v2.8.2, p. 17–18, lemmes 3.13 et 3.14 ; annonce de formalisation p. 50. Le compagnon fournit le développement quantitatif auquel ces lemmes renvoient.

**Type.** Suggestion de précision pour la future section de formalisation, **sans erreur identifiée dans les estimations du manuscrit**.

**Justification.** Le développement Lean actuel prouve la conséquence suivante : pour chaque hauteur polynomiale fixée et chaque `epsilon>0`, un seul seuil rend les comptages inférieurs à `M^epsilon` pour tous les coefficients et décalages admissibles. Dans le produit décalé, le degré est fixé avant ce seuil, les facteurs sont positifs et les décalages distincts. Les deux signes possibles de la racine sont comptés. Cette uniformité suffit aux raccords de comptage des hôtes.

La forme plus précise `exp(O(log M / log log M))` affichée dans les lemmes 3.13–3.14 n'est pas identique à cette conséquence : elle apporte un taux supplémentaire. La nouvelle preuve interne du diviseur et son application à Pell ne revendiquent pas encore ce taux. Pour présenter honnêtement la couverture de la V3, il convient donc de distinguer cette conséquence uniforme des lemmes quantitatifs complets, sauf si le taux plus fin est formalisé ultérieurement.

**Formulation anglaise proposée pour l'état actuel.**

> The Lean development verifies the uniform `M^epsilon` consequences of the polynomial-height Pell and split-product counts: after the height exponent, degree and positive error exponent are fixed, the threshold is independent of all admissible coefficients and shifts. The sharper displayed `exp(O(log M / log log M))` rate is outside this part of the present formal scope.

**Statut.** Proposition à réévaluer au moment de figer la V3, selon la couverture alors atteinte. Cette entrée documente une limite de la formalisation actuelle, pas une correction mathématique du papier ou du compagnon.

**Preuves.** [DivisorSubpolynomial.lean](../PaperCV282/DivisorSubpolynomial.lean), `card_divisors_le_rpow_eventually` ; [PolynomialPellCount.lean](../PaperCV282/PolynomialPellCount.lean), `pellBox_atMost_rpow_eventually` ; [PolynomialSplitProducts.lean](../PaperCV282/PolynomialSplitProducts.lean), `splitProductStart_atMost_rpow_eventually` ; [PolynomialSplitSolutions.lean](../PaperCV282/PolynomialSplitSolutions.lean) ; [MacroscopicOneSidedFibers.lean](../PaperCV282/MacroscopicOneSidedFibers.lean), `offsetProductNatFiber_atMost_rpow_eventually`.

## V3-S007 — Simplifier la sommation du secteur terminal en deux populations

**Document et emplacement.** Papier v2.8.2, p. 22–24, lemmes 3.22–3.24 et preuve de la proposition 3.25. Le plafond de la proposition 3.27 (p. 26) se conserve dans la même preuve.

**Type.** Suggestion de simplification de preuve démontrée, **sans erreur identifiée dans le manuscrit**.

**Justification.** Sur une tranche du plus grand départ `X ≤ max(x,y) < 2X`, poser `j=s+ktilde` et `m=B−3j−1`. Le vrai test du secteur 8 donne `m≥1`. Les composantes isolées fournissent des noyaux non triviaux, distincts et deux à deux premiers entre eux, présents dans les deux fenêtres. La borne déterminant implique qu'au plus un dépasse `floor(sqrt(6XB))`, donc chaque fenêtre possède au moins `m` petits noyaux. Le comptage des partenaires donne `X^epsilon`, sans supposer que le plus petit départ soit comparable à `X`.

Réunir tous les couples pour lesquels `m≥2`. Chaque plus grand départ contribue au moins une unité à l'énergie `choose(A_T(x),2)`. Le lemme 3.24 compte donc ces départs avec la borne `X^(2/3+epsilon)B²`, et les partenaires ajoutent seulement un facteur sous-polynomial. L'identité exacte `tau+j=B+D#`, avec `D#≤2`, donne un poids au plus `4Q_B`. Le facteur deux des orientations et `B²` s'absorbent dans l'erreur d'exposant.

Sur le complément `m≤1`, on a `3tau≤2B+8`, donc un poids au plus `8Q_B^(2/3)`. Le conteneur à un petit noyau et les partenaires comptent au plus `X^(3/4+epsilon)` couples. Cette séparation suffit sans sommation géométrique des strates de rang. Les fibres exactes du logarithme dyadique du plus grand départ couvrent tous les couples ; la borne macroscopique inférieure transporte uniformément la bande logarithmique et permet d'absorber leur nombre.

On retrouve exactement `M^epsilon (M^(2/3)Q_B+M^(3/4)Q_B^(2/3))`. Pour un plafond réel commun `T≥0`, la première branche utilise `min(T,w)≤4min(T,Q_B)` et la seconde conserve sa borne non plafonnée. Tous les seuils précèdent `T`. Aucune symétrie du choix canonique n'est supposée : seul le comptage emploie les coordonnées maximum et minimum.

**Formulation anglaise proposée.**

> Split the terminal population according to whether the index forces at least two small kernels in each window. In the first population, the binomial energy bounds the number of larger starts directly, while the uniform partner count and the pointwise bound `2^tau−1≤4Q_B` give the two-thirds term. In the complementary population, the index identity implies `3tau≤2B+8`, hence weight at most `8Q_B^(2/3)`; the one-kernel container gives the three-quarter term. Summing the larger-start dyadic slices proves Proposition 3.25. The same argument keeps any common nonnegative cap by replacing `Q_B` in the first term with `min(T,Q_B)`.

**Statut.** Proposition à examiner pour la V3. Preuve formalisée et relue indépendamment. Elle ne revendique ni un meilleur exposant ni les taux plus précis de Pell laissés ouverts dans V3-S006.

**Preuves.** [SectorEightWeights.lean](../PaperCV282/SectorEightWeights.lean), [TerminalSliceGeometry.lean](../PaperCV282/TerminalSliceGeometry.lean), [TerminalSliceCounting.lean](../PaperCV282/TerminalSliceCounting.lean), [SectorEightSliceMass.lean](../PaperCV282/SectorEightSliceMass.lean) et [SectorEightProfile.lean](../PaperCV282/SectorEightProfile.lean), `proposition_three_twenty_five` et `proposition_three_twenty_five_capped`.

## V3-S008 — Localiser le coût de suppression au masque

**Document et emplacement.** Papier v2.8.2, p. 27–28, théorème 4.1, équation (4.3) et première phrase de sa preuve.

**Type.** Suggestion de précision et de renforcement, **sans erreur identifiée dans le manuscrit**.

**Justification.** La formalisation conserve les ensembles réellement supprimés avant de les majorer par le bloc entier. Pour `A⊆I_N`, poser `M_B(A)=Σ_{x∈A}(2^{m_B(x)}−1)` et `D_Y(A)=A∩D_Y`, avec les mêmes supports complets, y compris `x−1`. La somme des vraies probabilités des sites supprimés est au plus `p(M_B(A)+|D_Y(A)|)`. La suppression des coordonnées de la cible Poisson ajoute exactement au plus `p|D_Y(A)|`.

La contribution totale de suppression est donc `p(M_B(A)+2|D_Y(A)|)`. Elle implique la forme globale imprimée, et peut être plus informative pour un masque clairsemé. Les autres termes restent `|A|`, `E_Y(A)` et `R2(A)` ; le facteur scalaire continue d'utiliser la moyenne propre `μ_A=|A∩G_Y|p`. La suggestion ne remplace pas cette moyenne par l'intensité ambiante.

**Formulation anglaise proposée.**

> For a mask A, set M_B(A)=Σ_{x∈A}(2^{m_B(x)}−1) and D_Y(A)=A∩D_Y. The deletion contribution can be sharpened to p(M_B(A)+2|D_Y(A)|), while the Stein factor continues to use μ_A=|A∩G_Y|p.

**Statut.** Proposition à examiner pour la V3. Le budget scalaire a été formalisé sur les vrais atomes de `F_Y`, pour toute coupure admissible, puis dans le modèle infini après mélange. La relecture indépendante valide ce renforcement. Les PDF n'ont pas été modifiés.

**Preuves.** [MaskedBadMass.lean](../PaperCV282/MaskedBadMass.lean), `maskedBadStartMass_le` et `masked_total_deletion_cost_le` ; [MaskedScalarTransfer.lean](../PaperCV282/MaskedScalarTransfer.lean), `theorem_four_one_scalar_conditional` ; [MaskedScalarFullConditioning.lean](../PaperCV282/MaskedScalarFullConditioning.lean), `theorem_four_one_scalar_full_FY`.

## Suivi des prochaines observations

Chaque nouvelle entrée indiquera le document, la version, la page et l'énoncé ; distinguera erreur, clarification et suggestion ; donnera une justification vérifiable, une formulation proposée, le statut d'intégration et un lien vers la preuve ou la note correspondante. Lorsqu'une observation sera réglée, son entrée conservera l'historique et identifiera la version du manuscrit qui l'a intégrée.

## V3-S009 — Une preuve soft commune à toutes les intensités

**Document et emplacement.** Papier v2.8.2, p. 29, preuve du théorème 4.3, de (4.10) à (4.9) ; compagnon, section B.3, p. 8–9.

**Type.** Suggestion de simplification de preuve démontrée, sans erreur identifiée dans le texte actuel.

**Justification.** La preuve du papier traite les intensités inférieures à un en rejouant le transfert hard au seuil soft. La formalisation obtient aussi cette plage directement à partir de B.2, au même seuil soft. Poser `ell = max(0, log λ)` et `K = max(1, λ)`. Dans la branche non triviale précisée ci-dessous, les deux facteurs de Stein donnent, pour les véritables coûts arithmétiques, une borne `2q + 3r + 6KP`, où

```text
q = exp(-(w-ell)/2 + ην),
r = exp(ell-w + ην),
P = N^(-1/3+ε/2).
```

Si `q + N^(-1/3+ε) ≥ 1`, la borne triviale en variation totale suffit. Sinon `q ≤ 1` entraîne `ell ≤ w`, donc `r ≤ q`. Puis `K = exp(ell)` et `w = o(log N)` permettent d'absorber `K` dans `N^(ε/2)`. Ainsi `KP ≤ N^(-1/3+ε) < 1` et `K ≥ 1` donnent aussi `P ≤ 1`, hypothèse du calcul du registre soft. On obtient `6 min(1, q + N^(-1/3+ε))`, sans hypothèse globale de croissance sur l'intensité. Le seuil en `N` est choisi avant la longueur dans toute la bande logarithmique fixée.

Les voisins exceptionnels conservent leurs vraies probabilités marginales et conjointes dans B.2. Le résultat porte à la fois sur la vraie loi du compte et sur la moyenne des distances conditionnelles sachant **tout** `F_Y` au seuil soft. Il ne déduit pas cette dernière conclusion d'un conditionnement au seuil hard.

**Formulation anglaise proposée.**

> The soft estimate also covers intensities below one directly at the same cutoff. Set ell = max(0, log lambda) and K = max(1, lambda). The two Stein factors give the same error ledger for all intensities. In the nontrivial range ell is at most w, and K is absorbed into the polynomial remainder using w = o(log N).

**Statut.** Proposition à examiner. Le passage est démontré et relu indépendamment ; il simplifie l'exposition et ne prétend ni optimalité du seuil, ni convergence à la frontière soft exacte. Les prémisses bibliographiques de Stein scalaire et du théorème des nombres premiers restent explicites.

**Preuves.** [SoftArithmeticTransfer.lean](../PaperCV282/SoftArithmeticTransfer.lean), `average_conditionalMaskedLaw_soft_le` ; [SoftPoissonRates.lean](../PaperCV282/SoftPoissonRates.lean), `soft_rate_minimum_of_budget` et `soft_rate_rpow_of_budget` ; [SoftRateAssembly.lean](../PaperCV282/SoftRateAssembly.lean), `theorem_four_three_soft` ; [FreeCutoffSoftRates.lean](../PaperCV282/FreeCutoffSoftRates.lean), `equation_four_ten`.

## Vérification du lot 12 — dictionnaires, sans nouvelle anomalie

Le théorème 5.1 et le corollaire 5.4 ont été raccordés aux vraies lois, avec toutes les positions et tous les mots conservés. Le cap marginal de (5.6) est appliqué avant la sommation, et la compatibilité dirigée inclut les chevauchements propres et croisés. La borne (5.2) possède une constante explicite 8 dans la formalisation, sous les entrées bibliographiques AGG/PNT déjà déclarées. Le régime critique et la contraction vers les statistiques du champ sont établis.

La construction effective de 5.4 fonctionne dès B≥8. Elle utilise k=floor(log₂(2B))+1 ; aux puissances de deux, ce nombre dépasse d’une unité le plafond choisi dans le papier, et les mêmes inégalités de taille donnent le minorant2^B/(32B). La possibilité de sélectionner le nombre voulu de mots dans la fenêtre critique est prouvée. Cette variante est un choix de présentation de la formalisation, sans correction demandée au manuscrit.

À l’issue du lot 12, les relectures n’avaient relevé aucune nouvelle erreur dans ces passages. Le registre comptait alors **une correction confirmée et neuf suggestions**. Lors de la préparation de la V3, la section consacrée à Lean pourra citer ces deux résultats et leurs limites précises à partir du [registre des déclarations](../PaperCV282/ENDPOINTS.md). À l’issue du lot 12, les corollaires 5.2,5.3 et5.5 restaient séparés et n’étaient pas encore annoncés comme formalisés ; ils ont été fermés au lot 13.

## V3-S010 — Donner l'espérance exacte du recouvrement d'un dictionnaire uniforme

**Document et emplacement.** Papier v2.8.2, p. 32, corollaire 5.3, équation (5.8) et sa preuve.

**Type.** Suggestion de renforcement, sans erreur identifiée dans la majoration actuelle.

**Résultat.** Si W est choisi uniformément parmi les m-sous-ensembles de l'espace des mots binaires de longueur B, avec 1≤m≤2^B, alors

```text
E_W Ω(W) = m(B−1)/2^B.
```

La formule s'entend pour B≥1 dans la présentation du papier. Elle est légèrement plus forte que la majoration par m(B−1)/(2^B−1) affichée en (5.8).

**Justification.** À chaque déplacement propre d, il existe exactement 2^d mots auto-compatibles. Le nombre total de paires ordonnées compatibles est 2^(B+d), dont 2^d diagonales ; il reste donc 2^d(2^B−1) paires distinctes. En multipliant par les probabilités d'inclusion sans remise m/2^B et m(m−1)/(2^B(2^B−1)), puis par le poids 2^(-d)/m, la contribution attendue de chaque déplacement est exactement m/2^B. La sommation sur les B−1 déplacements donne l'identité. Le cas m=1 est inclus.

**Formulation anglaise proposée.**

> For a uniformly chosen m-element dictionary, the expected overlap weight is exactly E_W Ω(W)=m(B−1)/2^B. At each proper displacement d, the number of ordered compatible distinct pairs is 2^d(2^B−1); combining the diagonal and off-diagonal inclusion probabilities gives m/2^B per displacement.

Cette égalité peut remplacer (5.8), avec une courte adaptation de la preuve. La suite par Markov et l'ordre de la fraction exceptionnelle restent inchangés. Il s'agit toujours d'un résultat sur une classe de dictionnaires déterministes ; le théorème de Poisson ne suppose pas un nouveau tirage de dictionnaire.

**Preuves.** [RandomDictionaryWordCount.lean](../PaperCV282/RandomDictionaryWordCount.lean), `card_selfOverlapWords`, `card_compatibleSecondWords` et `sum_distinct_directedOverlapWeight` ; [RandomDictionary.lean](../PaperCV282/RandomDictionary.lean), `dictionaryAverage_eq_expectation` et `dictionaryFraction_eq_probability` ; [RandomDictionaryOverlap.lean](../PaperCV282/RandomDictionaryOverlap.lean), `average_overlapWeight_eq`, `equation_five_eight` et `dictionaryFraction_overlapWeight_gt_le`.

**Statut.** Proposition à examiner par l'auteur pour la V3. Le tirage sans remise, les comptes exacts et leurs probabilités sont démontrés. Les PDF sont inchangés. Le registre atteint désormais **une correction confirmée et dix suggestions**.


## Bilan du lot 14 — Marques exactes et loi composée

Le théorème **5.6**, y compris ses versions signée et non signée et le taux uniforme, et le corollaire **5.7** sur le vrai compteur de fenêtres constantes sont désormais formalisés sous les entrées bibliographiques déclarées. Les valeurs locales et la représentation composée avec tailles géométriques indépendantes sont démontrées. La V3 pourra citer ces résultats et leurs [déclarations précises](../PaperCV282/ENDPOINTS.md).

La formalisation garde explicitement la longueur de base L dans la masse de défauts et R2, et Q=L+E+1 dans les supports maximaux. Elle confirme le rôle essentiel de (5.15). Le cylindre premier peut être choisi égal au maximum de Y et du seuil couvrant le champ, ce qui rend le conditionnement par tout F_Y explicite. Les deux événements de bord sont ceux du texte ; aucune erreur d'indice n'a été relevée.

Aucune nouvelle correction du papier n'est confirmée dans ce lot. Le registre reste à **une correction confirmée et dix suggestions**. Le recours à une égalité presque sûre dans la preuve Lean de (5.16) ne suffit pas à conclure que l'égalité imprimée serait erronée. Le champ spatial à toutes marques et sa limite diffuse restent distincts des résultats 5.6–5.7 acquis ; ils ne devront pas être annoncés comme complètement formalisés à ce stade. Les PDF restent inchangés.


## Bilan du lot 15 — Champ spatial complet, limite diffuse et niveaux croissants

Le **théorème 1.1** est maintenant formalisé sur le vrai champ spatial signé à toutes marques : comparaison sur la grille dénombrable avec le coefficient1/√2, conséquence pour le compteur de départs, puis vraie convergence faible vers le processus de Poisson diffus. La version Lean conserve les sous-suites de tailles et l'intensité mobile du papier. La cible est construite par un nombre de Poisson et des marques indépendantes, avec positions uniformes sur[1,2], excès géométriques et signes équiprobables ; ses identités de lois et son support sont prouvés.

Toute la partie **5.8(i)** est également acquise, avec les budgets hard(5.18), mobile(5.19) et la borne(5.20), sous le conditionnement par tout F_Y correspondant. La version signée étiquetée de **5.9** et le changement exact de coordonnées r=e−d sont démontrés. La formalisation emploie pour les queues le choix simple E=3⌈V/log2⌉ ou son analogue mobile, suffisant dans les budgets considérés. C'est un choix de preuve, sans correction demandée au texte.

La bijection entre comptes exacts à masse finie et leurs seuils est mesurable dans les deux sens et conserve **exactement** la variation totale, même pour le chemin entier des compteurs réels conditionnés. Ce fait ne ferme pas la comparaison agrégée plus forte de5.8(ii), sa version signée niC.1. Ces obligations et la limite Poisson–Gauss5.10 devront rester présentées comme ouvertes dans une description de la couverture actuelle.

La V3 pourra utiliser les [déclarations précises](../PaperCV282/ENDPOINTS.md) pour citer ces acquis, en indiquant les arguments bibliographiques AGG de processus/PNT. Aucune nouvelle erreur du papier n'a été confirmée. Le registre reste à **une correction confirmée et dix suggestions** ; les PDF demeurent inchangés. L'avertissement du bilan14 sur le champ spatial est désormais levé par les preuves du lot15.


## V3-S011 — Identifier précisément l'entrée de Stein directionnelle

**Document et emplacement.** Compagnon technique v2.8.2, p. 10–12, dérivation directionnelle autour de (C.2)–(C.5).

**Type.** Suggestion d'explicitation bibliographique, **sans erreur identifiée**. Le texte distingue déjà le facteur directionnel de la comparaison agrégée ; la proposition précise ce qui est emprunté à la littérature et ce qui est démontré ensuite.

**Justification.** La formalisation utilise `DirectionalSteinFactorsStatement`, qui fournit une solution de l'équation de Stein multivariée et deux bornes de formes quadratiques de son Hessien, pour des intensités positives en dimension au moins deux. L'entrée reprend la forme publiée dans Röllin, *On the Optimality of Stein Factors*, arXiv:0706.0879v3, p. 5, équation (3.1), reproduisant le lemme 3 de Barbour (1988). Les bornes entrée par entrée, la sommation des poids géométriques, l'identité de remplissage indépendant de Poisson et la comparaison par graphe sont ensuite dérivées. La comparaison arithmétique ou une erreur de variation totale ne fait pas partie de cette entrée.

**Formulation anglaise proposée.**

> We use the multivariate Poisson Stein solution and its two quadratic-form Hessian estimates, in the form recorded by Röllin, equation (3.1), reproducing Barbour's Lemma 3. The entrywise directional bounds, the cancellation of the independent Poisson filling, and the dependency-graph comparison are derived below. In particular, the finite aggregated comparison is not itself a literature input.

**Statut.** Proposition à examiner par l'auteur. La frontière formelle comporte désormais quatre propositions bibliographiques explicites ; aucune n'est présentée comme un nouvel axiome Lean ni comme un résultat prouvé par l'audit des axiomes. Cette suggestion ne demande pas de remplacer l'énoncé C.1 par un autre.

**Preuves et limites.** [DirectionalSteinInput.lean](../PaperCV282/DirectionalSteinInput.lean), [DirectionalHessian.lean](../PaperCV282/DirectionalHessian.lean), [PoissonFillingIdentity.lean](../PaperCV282/PoissonFillingIdentity.lean), [DirectionalPoissonComparison.lean](../PaperCV282/DirectionalPoissonComparison.lean) et [SignedAggregateComparison.lean](../PaperCV282/SignedAggregateComparison.lean). L'analogue arithmétique signé est compilé et suffit aux conclusions de 5.8–5.10. Il conserve une masse de relations complètes de valeurs à longueur `Q=L+E+1` et `2*(Q+1)≤Y` ; le C.1 imprimé utilise la masse relative `R2(N,Q)` et `2Q<Y`. Aucun raccord exact entre ces formules n'est encore revendiqué, donc C.1 reste **partiel dans le comptage strict**. C'est une limite de couverture, sans erreur du compagnon identifiée.


## Bilan du lot 16 — Comparaison agrégée et limite Poisson–Gauss

Le **théorème 5.8(ii)** est désormais formalisé avec le budget `I+logΛ≤V−cν`, le vrai conditionnement par tout `F_Yhard` et tous les excès conservés. La borne est `2 exp(−c′ν)+N^(−1/3+ε)`, uniformément avant la longueur et l'événement conditionnant, pour `0<c′<c` et `ε>0` ; la convergence utilise `ε<1/3`. La comparaison signée et non signée et le raccord littéral aux coordonnées `r=e−d` ferment aussi le **corollaire 5.9**. Le chemin entier des seuils conserve exactement la distance des comptes exacts. Voir [SignedAggregateHardBudget.lean](../PaperCV282/SignedAggregateHardBudget.lean) et [AggregateMovingCoordinates.lean](../PaperCV282/AggregateMovingCoordinates.lean).

Le **théorème 5.10** porte sur les vrais compteurs arithmétiques conditionnés, le long de tailles quelconques tendant vers l'infini, avec `d→∞`, `d/logN→0` et convergence de la phase. Le centrage et la normalisation utilisent la véritable intensité `Λ_N`. Pour chaque segment fini de niveaux inférieurs et chaque ensemble fini de niveaux critiques, la limite est le produit d'une gaussienne de covariance `2^(−max(j,k))` et de Poisson indépendants de moyennes `2^(θ−r−1)`. L'indépendance limite est démontrée à partir de la même configuration de Poisson sous-jacente. Les innovations et la récurrence AR(1) sont identifiées sur chaque segment fini. Voir [PoissonGaussianTheorem.lean](../PaperCV282/PoissonGaussianTheorem.lean) et [GaussianThresholdAR.lean](../PaperCV282/GaussianThresholdAR.lean).

Cette preuve de limite faible n'ajoute aucune prémisse de CLT. Elle ne fournit pas les taux quantitatifs de Berry–Esseen, les estimations locales ou les déviations modérées de D.1, ni les raffinements ultérieurs de trajectoires. Les réserves du bilan 15 concernant les parties agrégées de 5.8–5.9 et la limite 5.10 sont levées ; la réserve littérale sur C.1 est maintenue pour les raisons indiquées en V3-S011. Le comptage strict devient **38/61 pour l'article et 3/8 pour le compagnon**, avec la même convention de dénominateurs.

Aucune nouvelle erreur du papier ou du compagnon n'est confirmée. Le registre contient désormais **une correction confirmée et onze suggestions**. Les PDF restent inchangés.


## V3-S012 — Donner une version effective de la formule locale de Poisson

**Document et emplacement.** Article v2.8.2, p.39, paragraphe précédant (6.7), et compagnon technique, D.1, formule locale de Stirling.

**Type.** Suggestion de renforcement explicite, **sans erreur identifiée**.

**Justification.** Le terme relatif `1+O(1/n)` peut être remplacé par une correction indépendante de l'intensité : pour tout `n≥1` et `λ>0`,

`p_λ(n)=exp(−δ_n) exp(−λ h(n/λ))/√(2πn)`, avec `0≤δ_n≤1/(12n)`.

L'erreur relative est donc au plus `1/(12n)`, uniformément en toute intensité positive. La preuve télescope l'inégalité de Robbins puis utilise la limite de Stirling démontrée dans mathlib. Elle n'introduit pas une approximation locale comme hypothèse.

**Formulation anglaise proposée.**

> For every integer n≥1 and every λ>0, one has p_λ(n)=exp(−δ_n) exp(−λh(n/λ))/√(2πn), where 0≤δ_n≤1/(12n). In particular, the relative error in the local approximation is at most 1/(12n), uniformly over all positive intensities.

**Preuves.** [PoissonStirlingBounds.lean](../PaperCV282/PoissonStirlingBounds.lean), `poisson_local_exact`, `poisson_local_bounds` et `poisson_local_relative_error` ; [PoissonResolutionBudget.lean](../PaperCV282/PoissonResolutionBudget.lean), `poisson_atom_reciprocal_le`. Le cas `n=0` conserve sa formule exacte `exp(−λ)` ; cette écriture avec racine de n ne s'y applique pas.

**Statut.** Proposition à examiner par l'auteur pour la V3. La borne précise peut remplacer le O local et expliciter le coût de résolution. Elle ne dispense pas des arguments séparés de Berry–Esseen, de développement central de l'entropie ou de déviation modérée. Les PDF restent inchangés.

## Bilan du lot 17 — C.1 exact et conditionnements du §6

La réserve du lot16 sur **C.1** est levée : la formule non signée utilise exactement `R2(N,Q)`, `Q=L+E+1` et le seul seuil `2Q<Y`, y compris `E=0`. Les deux signes sont conservés dans la comparaison directionnelle puis sommés à chaque paire d'excès fixée avant la borne relative. Voir [UnsignedAggregateC1.lean](../PaperCV282/UnsignedAggregateC1.lean). Aucune modification de l'énoncé du compagnon n'est nécessaire.

Les **lemmes6.1 et6.2**, le **théorème6.3** et le **corollaire6.4** sont formalisés sur les véritables lois et noyaux conditionnels. La variable enregistrée de6.1 peut prendre ses valeurs dans un espace mesurable arbitraire. La positivité après résolution du compteur est démontrée ; le futur entier et tout segment inférieur fini conservent la bonne loi cible et le coût exact. Le résultat presque sûr emploie le même espace de signes à toutes les échelles, sans indépendance entre celles-ci. Le budget suffit lui-même à obtenir la condition de profondeur.

Le taux agrégé **(6.5)** est prouvé pour toutes les intensités positives. Sous **(6.7)**, sur une bande logarithmique explicite, l'erreur divisée par la vraie masse de Poisson est au plus `40√(2π)exp(1/12) exp(−cν/2)+N^(−1/6)→0`. Cela donne directement le contrôle du vrai futur après résolution. La réduction centrale avec coefficient `3/2`, les raffinements quantitatifs restants de D.1 et le dernier paragraphe de6.4 gardent leurs réserves.

Le décompte strict atteint **42/61 dans l'article et4/8 dans le compagnon**. Les quatre entrées bibliographiques explicites restent inchangées. Aucune nouvelle erreur du papier n'est confirmée : le journal contient **une correction confirmée et douze suggestions**. Les sources du papier et du compagnon pourront accompagner leur future V3, avec les déclarations et le commit qualifié précisément indiqués.

## Bilan du lot 18 — Équation (6.3) à petite intensité

La conséquence relative du paragraphe précédant le théorème 6.3 est maintenant
formalisée. Sous `I(C)≤V−cν`, pour tout événement positif du vrai champ premier
dur et sur une bande logarithmique fixe, la distance en variation totale
conditionnelle divisée par `λ` est au plus `20(exp(−cν/2)+N^(−1/6))`.
Si `λ→0`, chacune des vraies probabilités `P(Z>0 | C)` et `P(Z=1 | C)`
est donc équivalente à `λ`. La preuve donne en plus une erreur relative
explicite d'au plus `20(exp(−cν/2)+N^(−1/6))+λ`.

Voir [SmallIntensityConditioning.lean](../PaperCV282/SmallIntensityConditioning.lean),
`small_intensity_relative_bound` et `equation_six_three`. L'équation (6.3)
est distincte du théorème 6.3 : aucun résultat numéroté n'est compté deux fois.
La réserve « relatif à petite intensité » du bilan de couverture précédent
est levée. Aucun changement du texte mathématique n'est nécessaire ; aucun
nouveau point de correction ou suggestion n'est ajouté. Le journal conserve
**une correction confirmée et douze suggestions**, les PDF restent inchangés.

## Bilan du lot 19 — Budget central avec coefficient 3/2

Le développement central annoncé après (6.7), et détaillé en D.1, est prouvé
avec l'arrondi entier borné : si `λ→∞`, `n=λ+t√λ+O(1)` et
`t=o(λ^(1/6))`, alors `λh(n/λ)=t²/2+o(1)` et `log n=log λ+o(1)`.
Une borne cubique explicite contrôle le reste d'entropie.

Sous `I+(3/2)log λ+t²/2≤V−cν`, toute marge `0<c'<c` donne le budget
complet (6.7), puis la positivité de `C∩{Z=n}` et la convergence de la vraie
loi conditionnelle de tout le futur vers sa cible de durées géométriques.
La bande logarithmique est une conséquence du budget. Voir
[CentralResolutionBudget.lean](../PaperCV282/CentralResolutionBudget.lean),
`central_resolved_future`.

Cette preuve précise le sens de « with a fixed margin » déjà présent dans
l'article. Le coefficient 3/2 demeure un budget suffisant, sans affirmation
de seuil optimal. Aucun changement du papier ni nouvelle suggestion n'est
nécessaire. Le transfert local central du taux doux, Berry–Esseen et les
queues de déviation modérée restent distincts. Le registre conserve
**une correction confirmée et douze suggestions** ; les PDF restent inchangés.

## V3-S013 — Compter les fenêtres profondes dans une seule population

**Document et emplacement.** Papier p.42, preuve de la proposition7.3 et
équations(7.8–7.9) ; compagnon E.5 p.20, estimation mésoscopique.

**Type.** Suggestion de simplification démontrée, sans erreur du texte actuel.

Le comptage uniforme de Pell s'applique directement à toute population finie
de départs jusqu'à2M. Il donne, pour les départs profonds d'un masque s,
`Σ_{x∈s} P(J_x,L=1) ≤ |s|2^−L + exp(C L/log L)2^−g_L`.
Les coupures suivent sans découpage supplémentaire en tranches dyadiques
ni facteur extérieur L. Le taux exponentiel n'est pas annoncé meilleur.
Les arguments bibliographiques de Shorey, PNT et Nicolas–Robin restent explicites.

**Preuves.** [IntermediateDefectCount.lean](../PaperCV282/IntermediateDefectCount.lean),
`global_two_defect_count_eventually`, et
[DeepStartMass.lean](../PaperCV282/DeepStartMass.lean), `deep_mass_bound_eventually`.

**Formulation anglaise proposée.**

> The uniform Pell box counts all two-defect windows in an arbitrary finite population up to twice the ambient height at once. The deep first moment is therefore bounded by the baseline population mass plus exp(C L/log L)·2^(−g_L), without a separate dyadic-slice factor. The same argument applies to every upper cutoff in that population.

**Statut.** Proposition à examiner par l'auteur ; les PDF ne sont pas modifiés.

## Bilan du lot20 — Frontière, départs profonds et horloges

Les résultats7.1–7.3 et les lemmes E.1–E.3 sont formalisés sur les vrais
événements arithmétiques. La frontière microscopique fournit la masse q_L,
la localisation conditionnelle, la marge1/12 et la loi limite géométrique
sur l'horloge des nombres premiers. Les configurations prolongées par zéro
sont stables sous les coupures mésoscopiques du papier. Les identités affines
de masse du bord et de queue sur les prochains premiers sont établies ;
le théorème7.10 complet et le mélange des deux sources restent ouverts.

La réserve V3-S006 est levée pour le taux précis des deux-défauts intermédiaires,
sous Nicolas–Robin explicite ; elle n'est pas levée globalement pour3.13/3.14/A.2.
La frontière bibliographique active passe de quatre à sept propositions :
LS uniforme, Shorey carré et la borne historique de Nicolas–Robin s'ajoutent.
Elles doivent figurer dans la future description de la formalisation V3.

Aucune nouvelle erreur du papier n'est identifiée. Le registre compte désormais
**une correction confirmée et treize suggestions**, dont la simplification
V3-S013. Les PDF et les preuves historiques restent inchangés.

## V3-S014 — Simplifier la correction du préfixe contenu

**Document et emplacement.** Papier p.43, équation(7.11) et preuve du théorème7.4.

**Type.** Suggestion de simplification démontrée, sans erreur du texte actuel.

Le premier moment masqué déjà obtenu dans la proposition7.3 s’applique aux
vrais départs exclus à droite du préfixe. Leur somme est au plus
`L·2^(-L)+2exp(-c logM/loglogM)`, uniformément dans la bande logarithmique.
La comparaison pour `W=C_L+Σ_(2≤x≤M−L+1)J_x,L` peut donc ajouter seulement
`2^(-π(L))+O(L·2^(-L))`, après augmentation de la constante du reste profond
présent dans(7.10). Le terme `2^(-L)M^(1/2+o(1))` de(7.11) reste correct ;
il n’est pas nécessaire avec ce premier moment global. Cette simplification
préserve les entrées bibliographiques explicites des preuves précédentes.

**Preuves.** [PrefixContainedBounds.lean](../PaperCV282/PrefixContainedBounds.lean),
`overflow_mass_eventually` et `theorem_seven_four_contained_prefix`.

**Formulation anglaise proposée.**

> The masked prefix first-moment bound applies directly to the excluded rightmost starts. Their total mass is at most L·2^(−L)+O(exp(−c log M/log log M)). Thus the additional contained-prefix correction can be written as 2^(−π(L))+O(L·2^(−L)), after changing the constant in the existing deep-start remainder.

**Statut.** Proposition à examiner par l’auteur ; les PDF restent inchangés.

## Bilan du lot21 — Préfixe, enveloppes presque sûres et champ signé relatif

Les résultats7.4,7.5 et7.7 sont formalisés. Les enveloppes presque sûres
portent sur le vrai plus long run, pour tous les préfixes assez grands.
La comparaison relative conserve toutes les marques, les signes, les
positions x/M et la vraie loi conditionnelle pour F_Y. La factorisation
avec l’enregistrement microscopique B_L est obtenue à erreur o(λ), donc
o(q_L+λ), sans indépendance exacte à taille finie.

Le décompte strict atteint48/61 dans l’article et reste7/8 dans le compagnon.
Le transport macroscopique7.6 et les mélanges complets7.8–7.10 conservent
leurs réserves. Les sept propositions bibliographiques actives restent
inchangées. Aucune nouvelle erreur du papier n’est identifiée : le registre
contient **une correction confirmée et quatorze suggestions**, dont V3-S014.
Les fichiers source du papier et du compagnon pourront accompagner la future
V3, avec son périmètre formalisé et le commit précisément indiqués.
