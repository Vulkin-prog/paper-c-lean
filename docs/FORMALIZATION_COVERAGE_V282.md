# Couverture du papier C v2.8.2 et du compagnon — après le lot 9

**Environ 60 % du travail total de formalisation est acquis ; une fourchette prudente est 50–65 %. Il reste donc environ 35–50 % de l’effort.** Cette estimation porte sur l’ensemble de l’article et du compagnon, avec les modèles, les preuves réutilisables et les raccords nécessaires. Elle ne mesure ni la proportion de lignes Lean ni le temps déjà passé.

Le comptage strict des énoncés donne **25 résultats complets sur 61 dans l’article, soit 41,0 %**, contre 16/61 après le lot 8. Neuf résultats supplémentaires reçoivent le crédit complet : 2.5, 2.8, 3.1, 3.22, 3.23, 3.25, 3.26, 3.27 et 4.4. Le compagnon conserve 1/8 énoncé nommé complet ; ses preuves intermédiaires sont souvent partiellement réutilisables. Les deux fractions ne s’additionnent pas : plusieurs énoncés du compagnon développent les mêmes résultats que l’article.

Le présent bilan conserve la méthode et les 105 unités d’effort relatif du bilan initial du lot 9. Il évalue les sources finales compilées et leurs signatures. Le contrôle final communiqué par la tâche principale a réussi : construction globale, audit des 830 déclarations, huit tests du garde-fou et empreinte du cœur historique inchangée. La référence de publication reste dans le rapport de validation séparé. Il ne s’agit pas d’une nouvelle qualification Palomar.

## Ce que le lot 9 termine

La chaîne arithmétique nécessaire aux profils globaux est maintenant fermée. Le secteur terminal est traité sur les tranches du **plus grand départ**, sans imposer que les deux départs soient comparables. Les noyaux et déterminants effectifs donnent les partenaires et le conteneur ; la somme des tranches conserve le terme M^(3/4)Q_B^(2/3) du texte. Les profils brut, interpolé et plafonné sont disponibles pour les relations relatives et pour toutes les relations de valeurs. Ils s’appliquent au véritable intervalle [⌈M^δ⌉,M), aux blocs dyadiques et aux intervalles à rapport borné.

Les seuils sont choisis avant les longueurs variables, les masques, les coupures adéquates et les plafonds. Les extensions à rapport borné utilisent un κ naturel fixé ; tout rapport réel fixé est couvert en le majorant par un entier. Les sommes portent sur des paires ordonnées, et Q_B reste exactement 2^(L+1).

Le corollaire 2.5 dispose maintenant de ses deux bornes ponctuelles pour tout second membre affine et de ses vraies espérances masquées dans toute la bande logarithmique. Le lemme 2.8 couvre les recouvrements impossibles et les paires touchantes. Le corollaire 4.4 donne l’espérance, le **second moment factoriel** et la variance du vrai compteur infini, aux taux critiques annoncés. Ces moments sont prouvés directement ; aucune convergence de moments non bornés n’est déduite de la seule distance en variation totale.

Le corollaire 2.6 était déjà couvert dans le lot précédent par le modèle infini, les atomes positifs de F_Y et les sommes de mots. Le lot 9 ajoute les dictionnaires et la somme des erreurs absolues sur les masques macroscopiques, avec le facteur exact |W|/2^B et un seuil indépendant du dictionnaire. Un `Finset` représente des mots distincts.

## Méthode de comptage

Les 61 énoncés sont les Lemma/Theorem/Proposition/Corollary numérotés des §§2–7 de l’article. Les théorèmes introductifs 1.1–1.3 sont des reformulations et ne sont pas comptés deux fois. Définitions, preuves intermédiaires, remarques et questions futures du §8 ne créent pas de nouvelles lignes ; leur travail nécessaire est inclus dans les blocs d’effort. Les pages ci-dessous sont celles du PDF fourni.

« Complet » signifie que toutes les conclusions mathématiques de l’énoncé sont couvertes par les représentations explicites compilées ou une spécialisation historique vérifiée. Les formulations équivalentes à exposant ε ou à puissance entière de o(1) sont acceptées. « Partiel » conserve un taux plus fort, une branche ou une généralité manquante. « Réemploi non raccordé » désigne des preuves pertinentes qui ne donnent pas encore ensemble l’énoncé actuel. « À établir / non identifié » n’exclut pas l’existence de briques utiles dans mathlib.

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifiés |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 1 | 3 | 0 | 0 |
| §5 | 10 | 0 | 1 | 4 | 5 |
| §6 | 4 | 0 | 0 | 0 | 4 |
| §7 | 10 | 0 | 5 | 1 | 4 |

Le nombre de théorèmes Lean n’intervient pas dans ce calcul. Un résultat du papier peut demander des dizaines de lemmes ; une seule preuve historique peut servir plusieurs chapitres. Le cœur arithmétique est beaucoup plus avancé que les lois probabilistes de la seconde moitié du texte.

## Estimation de l’effort sur l’ensemble des deux textes

Les 19 blocs conservent exactement leurs poids antérieurs, pour un total de **105 unités relatives**. Seuls les crédits justifiés par les résultats du lot 9 changent. Le calcul donne 56,25–68,42 unités acquises, soit environ **54–65 %** ; la présentation 50–65 % arrondit volontairement la borne basse vers l’extérieur. Le point central « environ 60 % » aide à situer l’avancement et n’est pas une mesure objective. La fourchette précédente était 45–60 %. Une grande partie des briques terminales était déjà créditée avant leur assemblage ; leur fermeture ne doit donc pas être comptée une seconde fois.

| Bloc mathématique | Poids | Acquis après lot 8 | Acquis après lot 9 |
|---|---:|---:|---:|
| Modèle, Fourier, arbres et pivots | 6 | 85–95 % | 90–98 % |
| Runge croissant et défauts | 8 | 90–100 % | 95–100 % |
| Probabilités ponctuelles et moments à une fenêtre | 4 | 65–85 % | 100 % |
| Canal canonique, résolution, quotient et cellules | 6 | 90–100 % | 90–100 % |
| Hôtes globaux, masse rationnelle et CRT | 5 | 85–95 % | 85–95 % |
| Secteurs 1–7 et hôtes de composantes | 8 | 90–98 % | 90–98 % |
| Pell et split-products, y compris taux précis | 4 | 55–75 % | 55–75 % |
| Secteur terminal, énergie, profils globaux et minorants | 8 | 35–55 % | 95–100 % |
| Deux coupures et calcul uniforme des selles | 7 | 20–40 % | 20–40 % |
| Transfert TV, rétention douce et moments | 7 | 30–50 % | 50–65 % |
| Dictionnaires, recouvrements et constructions | 5 | 10–20 % | 10–20 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 35–50 % | 35–50 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 10–20 % | 10–20 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 5–15 % | 5–15 % |
| Frontière microscopique et rang d’incidence | 6 | 20–35 % | 20–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35–55 % | 35–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 30–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 20–40 % |
| Mélange des deux sources et horloges affines | 5 | 5–15 % | 5–15 % |

Cette estimation suppose des entrées de littérature explicitement transcrites et auditées quand elles sont nécessaires, selon la convention du périmètre historique. Formaliser aussi toutes les démonstrations des résultats externes de la bibliographie serait un objectif plus large et changerait le dénominateur. Une prémisse nouvelle ne peut pas être assimilée à une preuve interne ni être dissimulée dans un import.

## Limites qui restent réellement ouvertes

Les profils globaux ne rendent pas complets tous leurs lemmes auxiliaires sous leur forme la plus forte. La proposition 3.19 reste **partielle** : l’exclusion au seuil effectif 6c#>B ferme le secteur 4, mais ne prouve pas l’énoncé pour tout α>0 fixé. Les comptes de Pell et de produits décalés donnent uniformément M^ε, suffisant aux profils ; ils ne donnent pas encore le taux exp(O(log M/log log M)) de 3.13, 3.14 et A.2. Les comptes harmoniques ferment les hôtes principaux de 3.18, avec une enveloppe Euler élémentaire ; le raffinement exp(O(√B/log B)) de 3.17 et de la seconde clause de 3.18 reste à démontrer.

Le conditionnement du corollaire 2.6 est bien acquis : la partition en atomes positifs engendre exactement F_Y. La formulation imprimée « odd prime divisor » doit toutefois se lire avec une **valuation impaire**, comme le précise le contexte de la page précédente et la note de manuscrit. L’API abstraite d’espérance conditionnelle pourrait améliorer la présentation ; son absence ne rouvre pas les conclusions déjà établies sur ces atomes.

## Prochaine priorité : 4.1 et 4.2 / B.1

**4.1 est le prochain raccord probabiliste structurant.** Le modèle Rademacher infini, les probabilités conditionnelles sur bonnes fenêtres, l’indépendance hors voisinage et les nouveaux profils arithmétiques sont disponibles. Il reste à réunir ces éléments dans le transfert masqué exact, en conservant la moyenne propre du masque µ_A. Le facteur scalaire demandé est min(1,1/µ_A) ; il ne peut pas être remplacé par une intensité ambiante lorsqu’un masque est clairsemé. La comparaison du champ fini emploie, elle, le facteur non lissé. L’interface AGG historique ne fournit que 2(b₁+b₂), ce qui ne suffit pas à déclarer la version actuelle terminée.

Un premier sous-lot utile isolerait le théorème fini conditionnel, le coût exact de suppression des mauvais sites et l’identification des termes b₁/b₂ avec les masses maintenant prouvées. Il faudrait en parallèle établir ou transcrire fidèlement l’entrée de Stein sensible à l’intensité, puis transporter les lois vers le modèle infini. Le compagnon B.2 ajoute une autre obligation : conserver les indicateurs exceptionnels dans l’équation de Stein avec le facteur min(1,1/√λ). Cette rétention douce n’est pas contenue dans l’ancien théorème de suppression.

**4.2 et B.1 forment un chantier analytique parallèle.** `PaperCV11` apporte le produit de Rankin fini et l’équilibre dominant donnant 1/√2. Il reste la somme pondérée sur les nombres premiers avec terme principal PNT, la fonction Ei, l’existence et l’unicité des deux selles implicites, leurs développements de second ordre et les restes uniformes. Le résultat doit conserver une coupure libre avant de spécialiser aux deux selles, ainsi que les erreurs de partie entière et la normalisation du degré maximal sur tous les sites, y compris les mauvais. Un résultat à constante dominante indéterminée ne suffirait pas aux constantes de (4.6)–(4.7).

Ces deux chantiers ouvrent 4.3 puis les dictionnaires et champs marqués. Les anciennes marques exactes et égalités de lois finies/infinies sont directement réutilisables pour 5.6. En revanche, les dictionnaires croissants, les recouvrements, le champ signé, la comparaison agrégée sans perte en nombre de marques et la limite Poisson–Gauss demandent leurs propres raccords. La branche microscopique et le crossover viennent avec les obligations du compagnon E ; l’ancien input LS04 (Corollaire 1, équation (10)) ne remplace pas silencieusement sa borne (2−ε)π(B) de l’équation (14).

## Réemploi probabiliste concret conservé

| Brique vérifiée | Source réutilisable | Portée et limite |
|---|---|---|
| Modèle infini et cylindres | `InfiniteRademacher`, `FiniteCylinderCountTransport`, `InfiniteCountMoments` | Modèle, égalités de lois et vraies intégrales ; reconstruction inutile. |
| Bonnes fibres et graphe | `ConditionalStartProbability`, `ConditionalDependencyGraph` | Marginales exactes et indépendance hors voisinage, utilisables pour 4.1. |
| Marques exactes | `ExactLengthCountVectorTransfer`, `MarkedConditionalDependencyGraph`, `MarkedSteinChenTerms` | Comptes, graphes et lois finies/infinies ; nouveau contrôle uniforme du champ croissant restant. |
| Cible Poisson et Laplace | `PoissonVectorMass`, `SectionFourteenClosure`, `CorollaryFourteenEightCounts` | Marques fixes et atomes ; ne constitue pas déjà la comparaison TV signée ou une limite gaussienne. |
| Ancien Poisson masqué | `MaskedPoissonCanonical` | Loi critique qualitative conditionnelle aux prémisses historiques ; plein domaine et nouveaux taux non automatiques. |
| Préfixe infini | `CorollaryPrefixLawCanonical` | Couplages de bord et de débordement réutilisables ; taux actuels et bande complète restant. |

## Inventaire de tous les résultats numérotés de l’article

Les noms exacts des preuves et les éléments de provenance sont conservés dans le JSON associé. Les conclusions faibles ou spécialisées sont signalées explicitement dans ce tableau.

| Résultat | Page | Statut | Portée acquise ou travail restant |
|---|---:|---|---|
| 2.1 | 7 | Réemploi non raccordé | Identité de Fourier finie vérifiée ; raccord explicite au tuple arbitraire du modèle infini et conséquence en caractères à terminer. |
| 2.2 | 7 | Réemploi non raccordé | Bijection arbre/frontière et deux fenêtres acquises ; tuple arbitraire et caractère affine à réunir. |
| 2.3 | 8 | Complet | Borne de Runge complète par spécialisation historique, constante absolue explicite. |
| 2.4 | 8 | Complet | Bornes dyadiques complètes ; la somme macroscopique (2.4) est maintenant explicite. |
| 2.5 | 9 | Complet | Deux bornes affines ponctuelles et vraies espérances masquées dyadiques/macroscopiques, dans toute la bande. |
| 2.6 | 9 | Complet | Trois clauses acquises sur atomes positifs de F_Y ; extension macroscopique des dictionnaires ajoutée. |
| 2.7 | 9 | Partiel | Cas arbre et inclusion dans l’espace des cycles prouvés ; dimension cyclomatique générale encore en prémisse. |
| 2.8 | 10 | Complet | Incompatibilité des recouvrements et masse des paires touchantes N^(1+ε), avec analogue macroscopique. |
| 3.1 | 10 | Complet | Profils brut et interpolé, paires ordonnées et trois géométries ; seuil uniforme avant masque et coupure. |
| 3.2 | 11 | Complet | Dimension et hauteur du code rationnel historiques vérifiées. |
| 3.3 | 11 | Complet | Unicité du canal sur le véritable intervalle macroscopique, paramètre canonique A=3. |
| 3.5 | 12 | Complet | Résolution finie et classes de carrés des composantes, réutilisées dans les comptes effectifs. |
| 3.6 | 13 | Complet | Rang du quotient, capacité et défaut uniforme logarithmique. |
| 3.7 | 14 | Complet | Vrais hôtes de relations relatives et de toutes les relations de carrés : borne M^(3/2+ε). |
| 3.8 | 15 | Complet | Deux masses réellement filtrées par hauteur et masse géométrique en base 2, avec Q_B explicite. |
| 3.10 | 15 | Complet | Bornes finies des cellules résiduelles réutilisées hors de l’ancienne fenêtre critique. |
| 3.11 | 16 | Partiel | CRT pour certificats et sommes finies vérifiés ; généralité exacte de l’énoncé et série factorielle à réunir. |
| 3.12 | 17 | Complet | Trois secteurs couverts ; le secteur 2 dispose même d’une meilleure borne. |
| 3.13 | 17 | Partiel | Conséquence M^ε en hauteur polynomiale prouvée intérieurement ; taux exp(O(log M/log log M)) restant. |
| 3.14 | 18 | Partiel | Même distinction : compte M^ε acquis ; taux exponentiel plus précis restant. |
| 3.15 | 18 | Complet | Normalisation exacte du coefficient d·P, de sa classe de carrés et de sa hauteur. |
| 3.16 | 18 | Complet | Comptage à un côté M^ε en degré mobile ≥2 et alternative racine carrée pour un singleton. |
| 3.17 | 19 | Partiel | Compte harmonique/Euler suffisant pour M^(1+ε) ; raffinement exp(O(√B/log B)) non acquis. |
| 3.18 | 19 | Partiel | Borne principale M^(1+ε) acquise ; seconde clause plus précise dépend encore du raffinement de 3.17. |
| 3.19 | 20 | Partiel | Secteur 4 exclu au seuil 6c#>B ; l’énoncé pour tout α>0 fixé reste partiel. |
| 3.20 | 21 | Complet | Nombre macroscopique de départs avec deux défauts : M^ε. |
| 3.21 | 22 | Complet | Masse effective du secteur 6 : M^(1/2+ε)Q_B. |
| 3.22 | 22 | Complet | Paquet exact : noyaux égaux et non triviaux, coprimalité, divisibilité, 0<|Δ|≤4MB. |
| 3.23 | 23 | Complet | Partenaires X^ε et conteneur X^(3/4+ε), raccordés aux vraies tranches du plus grand départ. |
| 3.24 | 23 | Complet | Énergie décalée avec vrai second moment binomial fini et coupure T≤D√(XB). |
| 3.25 | 24 | Complet | Masse du secteur 8 avec les deux termes exacts M^(2/3)Q_B et M^(3/4)Q_B^(2/3). |
| 3.26 | 25 | Complet | Deux parités et vrais hôtes ; profils des valeurs complètes, bruts/interpolés, dans les trois géométries. |
| 3.27 | 26 | Complet | Deux masses réellement plafonnées ; seuil avant tout plafond T, même T≥0. |
| 4.1 | 27 | Partiel | Graphes conditionnels et arithmétique disponibles ; transfert exact avec moyenne propre du masque et facteur de Stein restant. |
| 4.2 | 28 | Partiel | Rankin fini et balance dominante disponibles ; deux selles implicites, Ei/PNT et restes uniformes restant. |
| 4.3 | 29 | Partiel | Ancienne loi critique qualitative réutilisable ; taux dur/doux et intensité croissante encore dépendants de 4.1, 4.2 et B.2. |
| 4.4 | 29 | Complet | Espérance, second moment factoriel et variance : trois taux critiques dans le vrai modèle infini. |
| 5.1 | 30 | Réemploi non raccordé | Graphes par site/mot disponibles ; recouvrements dirigés et loi quantitative du dictionnaire croissant à raccorder. |
| 5.2 | 31 | À établir / non identifié | Remplacement par signes indépendants : conclusion actuelle non identifiée. |
| 5.3 | 32 | À établir / non identifié | Dictionnaires aléatoires à faible recouvrement : compte et conclusion à établir. |
| 5.4 | 32 | À établir / non identifié | Construction explicite sans recouvrements : à établir. |
| 5.5 | 33 | À établir / non identifié | Loi quantitative des motifs à faible recouvrement : à établir à partir de 5.1. |
| 5.6 | 33 | Partiel | Marques fixes non signées disponibles ; champ complet, support maximal et absence de perte en nombre de marques restant. |
| 5.7 | 34 | Réemploi non raccordé | Atomes de marques finies réutilisables ; transformation en loi composée quantitative à raccorder. |
| 5.8 | 35 | Réemploi non raccordé | Deux niveaux d’approximation et intensité croissante ne découlent pas de l’ancienne convergence de Laplace. |
| 5.9 | 36 | Réemploi non raccordé | Modèle de signes disponible ; champ signé conjoint et demi-intensités indépendantes à formaliser. |
| 5.10 | 37 | À établir / non identifié | Limite conjointe Poisson–Gauss et covariance : nouvelle conclusion à établir. |
| 6.1 | 38 | À établir / non identifié | Atomes finis positifs acquis ; relèvement stable sur espaces standard boréliens arbitraires restant. |
| 6.2 | 39 | À établir / non identifié | Inégalité de conditionnement avec dénominateur max(p,q) : endpoint non identifié. |
| 6.3 | 39 | À établir / non identifié | Amincissement de Bernoulli réutilisable ; noyaux futurs complets, immigration inverse et coûts conditionnels restant. |
| 6.4 | 40 | À établir / non identifié | Briques de Markov/Borel–Cantelli possibles ; estimations environnementales sommables et conclusion uniforme restant. |
| 7.1 | 40 | Partiel | Événement exact au bord disponible ; asymptotique relative, rang d’incidence et localisation restant. |
| 7.2 | 42 | Partiel | Compte macroscopique M^ε disponible ; portée intermédiaire jusqu’à 2L² et taux plus précis restant. |
| 7.3 | 42 | Partiel | Estimations profondes partielles ; erreur relative et stabilité mésoscopique restant. |
| 7.4 | 42 | Partiel | Ancienne loi du préfixe infini critique disponible ; bande complète et nouveaux taux à raccorder. |
| 7.5 | 43 | À établir / non identifié | Enveloppes presque sûres asymétriques : conclusion et argument sommable à établir. |
| 7.6 | 43 | Partiel | Transport global non signé réutilisable ; champ croissant, taux et censure explicite restant. |
| 7.7 | 44 | Réemploi non raccordé | Marques et noyaux finis disponibles ; erreur relative o(λ_M), version signée et factorisation au bord restant. |
| 7.8 | 45 | À établir / non identifié | Loi rare à deux sources et localisation conditionnelle : endpoint actuel non identifié. |
| 7.9 | 46 | À établir / non identifié | Comparaison signée sur le réseau, deux horloges et poids mobiles : à établir. |
| 7.10 | 47 | À établir / non identifié | Crossover sous contraintes affines : algèbre disponible, loi quantitative à établir. |

## Compagnon complet

| Résultat nommé | Page | Statut | Portée acquise ou travail restant |
|---|---:|---|---|
| A.1 | 3 | Complet | Runge au niveau des coefficients : preuve historique complète. |
| A.2 | 4 | Partiel | M^ε acquis ; taux exp(O(log M/log log M)) non acquis. |
| B.1 | 7 | Partiel | Calcul libre, deux selles et restes PNT/Ei uniformes restant. |
| B.2 | 8 | À établir / non identifié | Rétention douce et deux facteurs sensibles à l’intensité : endpoint suffisant non identifié. |
| C.1 | 11 | Partiel | Comparaison agrégée, remplissage Poisson et lissage directionnel sans perte en nombre de marques restant. |
| E.1 | 17 | À établir / non identifié | Mineur d’identité de rang (2−o(1))π(B) aux trois départs de transition : à établir. |
| E.2 | 18 | Partiel | Algèbre de graphes disponible ; borne de rang E/(K+1) à raccorder explicitement. |
| E.3 | 19 | Partiel | Raccord exact des prémisses BS et des décalages ; somme microscopique relative restant. |

Les développements non numérotés A.3–A.5 sont inclus dans normalisation, quotient et exclusion alignée ; B.3 dans les transferts ; C.1–C.7 dans marques, agrégats et transport ; D.1–D.4 dans Gauss, chemins et conditionnement ; E.1–E.7 dans frontière, rang et crossover. Ils ne sont donc pas omis du pourcentage d’effort. A.1, A.2 et B.1 recouvrent directement des résultats de l’article : additionner 61 et 8 créerait un faux dénominateur indépendant.

## Sources et reproductibilité

Les deux PDF restent strictement ceux de la v2.8.2 fournis par l’utilisateur : article de 52 pages, compagnon de 23 pages. Aucune V3 future n’est traitée comme une source déjà livrée. Le modèle historique est conservé, avec Lean `leanprover/lean4:v4.32.0` et mathlib `v4.32.0` (révision `81a5d257c8e410db227a6665ed08f64fea08e997`). Le cœur de référence reste `b3cf107d2df629453a5da8e84f2bad29eea0bf94`.

| PDF | SHA-256 |
|---|---|
| Article | `263682a1f2aa8301f06bf811fea1f81f42cd4493ccc4e1b94242a66cacfbd623` |
| Compagnon | `60d6f110aa057ebd9b1c79eaa291bc42759b5f021ef03807d9405a7ec473b094` |

Bilan établi le 6 septembre 2026 par lecture des textes intégraux extraits, des registres et des signatures pertinentes dans `PaperC`, `PaperCV11` et `PaperCV282`. La comparaison porte sur le lot 8 publié au commit `031c7d5075d632a65813a7862b1869eb714b9261`. Les sources nouvelles sont compilées sous la version fixée ; la construction globale (4 270 étapes) et l’audit final ont réussi selon le résultat communiqué par la tâche principale. Le commit final est consigné dans le rapport de validation séparé. Le présent bilan ne remplace ni ce contrôle ni une qualification externe.
