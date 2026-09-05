# Registre des révisions proposées pour le papier et le compagnon — v3

Dernière mise à jour : 5 septembre 2026.

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

**Statut.** Proposition à examiner. L'identification et l'inégalité finie (3.24) sont formalisées sous leurs hypothèses explicites. Le module [FullHostAsymptotics.lean](../PaperCV282/FullHostAsymptotics.lean) établit aussi la borne `N^(3/2+o(1))` sur un bloc dyadique, uniformément sur les longueurs logarithmiques et sur tout masque de paires contenu dans ce bloc. Le passage aux fenêtres macroscopiques et le profil complet (3.25) restent à établir.

**Preuves.** [TwoWindowParity.lean](../PaperCV282/TwoWindowParity.lean), `startRelationEquivParityKernel` et `value_weight_le_four_start_weight_add_host` ; [ValueSquareRelations.lean](../PaperCV282/ValueSquareRelations.lean), `relationRho_ne_zero_iff_exists_nonempty_square_product` ; [TwoWindowSquareHosts.lean](../PaperCV282/TwoWindowSquareHosts.lean), `finite_equation_three_twenty_four_square_hosts`.

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

**Statut.** Proposition à examiner. La majoration de la somme pondérée et son application uniforme aux hôtes dyadiques sont vérifiées en Lean sans hypothèse de littérature externe. L'extension formalisée aux autres géométries reste à faire ; cette suggestion ne revendique pas une preuve complète de la proposition macroscopique.

**Preuves.** [RelationalHostBound.lean](../PaperC/Analysis/RelationalHostBound.lean), `sum_largeKernelWeight_le_sqrt_mul_exp` ; [FullHostAsymptotics.lean](../PaperCV282/FullHostAsymptotics.lean), `card_squareProductHosts_cast_le_exp_bound` et `card_squareProductHosts_uniformThreeHalves`. Le premier résultat est un lemme analytique historique réutilisé ; le raccord aux hôtes sans parité est nouveau.

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

## Suivi des prochaines observations

Chaque nouvelle entrée indiquera le document, la version, la page et l'énoncé ; distinguera erreur, clarification et suggestion ; donnera une justification vérifiable, une formulation proposée, le statut d'intégration et un lien vers la preuve ou la note correspondante. Lorsqu'une observation sera réglée, son entrée conservera l'historique et identifiera la version du manuscrit qui l'a intégrée.
