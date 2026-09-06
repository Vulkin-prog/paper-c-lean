# Couverture du papier C v2.8.2 et du compagnon — lot 12

**Environ 70 % de l’effort total est acquis, avec une fourchette prudente de 65–80 %.** La grille conserve les mêmes **19 blocs et 105 unités relatives**. Cette estimation porte sur l’article entier et son compagnon ; elle ne provient pas du nombre de déclarations Lean.

Le comptage strict atteint **30 résultats complets sur 61 dans l’article (49,2 %)**, contre 28 au lot 11. Les nouveaux résultats complets sont **le théorème 5.1 et le corollaire 5.4**. Le compagnon reste à **3/8**. Les deux fractions ne s’additionnent pas : plusieurs énoncés se recouvrent entre les documents. B.3 est une sous-section, pas un neuvième énoncé du compagnon.

« Complet » garde la frontière bibliographique explicite des lots précédents. Les bornes du champ utilisent le théorème AGG de processus et le reste du théorème des nombres premiers comme arguments déclarés. Leur démonstration interne n’est pas revendiquée. Les marqueurs et la contraction sont démontrés sans nouvelle prémisse bibliographique. L’audit des axiomes ne décharge pas les arguments des théorèmes. Voir les [hypothèses bibliographiques](../PaperCV282/LITERATURE_INPUTS.md).

## Résultats du lot

| Résultat | Portée démontrée |
|---|---|
| Théorème5.1, (5.2) | Champ complet indexé par position et mot ; cible produit de Poisson de paramètre2^(-B) à chaque coordonnée ; vraie loi infinie et moyenne conditionnelle sur tout F_Yhard. |
| (5.5)–(5.7) | Probabilité locale exacte selon compatibilité dirigée ; cap marginal avant sommation des paires séparées ; graphe exact et suppression réelle, avec tous les labels conservés. |
| (5.3)→(5.4) | Fenêtre centrée sur log₂(Nm), m≤N^(1/2−δ), intensité bornée déduite ; choixε=δ/6 et resteN^(-δ/2) ; convergence des vraies distances lorsqueΩ→0. |
| Restrictions et statistiques | Image de la vraie loi sous toute fonction du champ, identité de la loi composée et contraction de la distance ; même borne conditionnelle moyenne et inconditionnelle. |
| Corollaire5.4 | Famille explicite0^k1u1, cardinal≥2^B/(32B) dès B≥8, aucun recouvrement propre, y compris avec soi-même ; tout sous-dictionnaire aΩ=0 ; capacité suffisante dans la vraie fenêtre critique. |

Les mots sont des fonctions Fin B→F₂ et B=L+1. Le premier signe au sommetx−1 est prescrit. Le poidsΩ est la somme dirigée des chevauchements propres, divisée par le nombre de mots : il inclut les chevauchements entre mots distincts et ceux d’un mot avec lui-même. Le regroupement des erreurs en indicatrices de dictionnaire conserve le champ site×mot dans le théorème de Poisson.

La borne complète possède une constante absolue explicite 8. Pour chaque βMin>0,βMax>βMin,ε>0 etη>0, son seuil est choisi avant L et tout dictionnaire W. Le reste exponentiel s’écrit exp(−Vhard+ηνhard) pour toutη>0 ; le seuil dépend deη, et reste indépendant des mots et de leur nombre. Le produitΛ(1+Λ) et les trois monômesΛ,Λ^(11/6)m^(1/6),Λ^(4/3)m^(2/3) sont conservés. Les vraies masses de défauts, arêtes et relations plafonnées fournissent ces termes.

Les masses conditionnelles sont les rapports des probabilités réelles sur les atomes positifs des petits premiers. L’admissibilité prouve que le cylindre contient tous les premiers≤Yhard. La convergence porte sur la distance inconditionnelle et la moyenne des distances conditionnelles ; elle ne revendique pas une convergence presque sûre des noyaux.

La famille de marqueurs utilise k=floor(log₂(2B))+1. Ce choix diffère au plus d’une unité du plafond imprimé, aux puissances de deux exactes, et conserve le même minorant 32. La capacité critique est déduite du rapport log N/N→0 et de la fenêtre donnée ; elle n’est pas supposée. Les [déclarations précises](../PaperCV282/ENDPOINTS.md) et le [journal V3](PAPER_V3_REVISION_LOG.md) documentent cette variante sans l’attribuer à une erreur du papier.

## Comptage strict

| Partie | Énoncés | Complets | Partiels | Réemploi non raccordé | À établir / non identifié |
|---|---:|---:|---:|---:|---:|
| §2 | 8 | 5 | 1 | 2 | 0 |
| §3 | 25 | 19 | 6 | 0 | 0 |
| §4 | 4 | 4 | 0 | 0 | 0 |
| §5 | 10 | 2 | 1 | 3 | 4 |
| §6 | 4 | 0 | 1 | 0 | 3 |
| §7 | 10 | 0 | 5 | 1 | 4 |
| Compagnon | 8 | 3 | 4 | 0 | 1 |

La [matrice JSON](FORMALIZATION_COVERAGE_V282.json) conserve les 69 lignes documentaires avec leurs preuves et obligations. Les reprises introductives 1.1–1.3 ne sont pas recomptées. Les équations 5.2,5.4,5.5,5.6 et5.7 n’ajoutent pas cinq énoncés au dénominateur 61.

## Estimation de l’effort

Seul le bloc « dictionnaires » reçoit du crédit nouveau : de 10–20 % à 70–85 %, soit +3,00 à+3,25 unités. Le total passe de 65,75–76,07 à **68,75–79,32 unités sur 105**, donc **65,48–75,54 %**. Le milieu 70,51 % est communiqué comme « environ 70 % », avec la fourchette extérieure 65–80 %. Les outils génériques ne sont pas crédités une seconde fois dans les chapitres futurs.

| Bloc mathématique | Poids | Acquis après lot 11 | Acquis après lot 12 |
|---|---:|---:|---:|
| Modèle, Fourier, arbres et pivots | 6 | 90–98 % | 90–98 % |
| Runge croissant et défauts | 8 | 95–100 % | 95–100 % |
| Probabilités ponctuelles et moments à une fenêtre | 4 | 100 % | 100 % |
| Canal canonique, résolution, quotient et cellules | 6 | 90–100 % | 90–100 % |
| Hôtes globaux, masse rationnelle et CRT | 5 | 85–95 % | 85–95 % |
| Secteurs 1–7 et hôtes de composantes | 8 | 90–98 % | 90–98 % |
| Pell et split-products, y compris taux précis | 4 | 55–75 % | 55–75 % |
| Secteur terminal, énergie, profils globaux et minorants | 8 | 95–100 % | 95–100 % |
| Deux coupures et calcul uniforme des selles | 7 | 95–100 % | 95–100 % |
| Transfert TV, rétention douce et moments | 7 | 100 % | 100 % |
| Dictionnaires, recouvrements et constructions | 5 | 10–20 % | 70–85 % |
| Marques, signes, comparaison agrégée et clusters | 7 | 35–50 % | 35–50 % |
| Niveaux croissants et limite Poisson–Gauss | 5 | 10–20 % | 10–20 % |
| Conditionnement, chemins et contrôle presque sûr | 5 | 20–35 % | 20–35 % |
| Frontière microscopique et rang d’incidence | 6 | 20–35 % | 20–35 % |
| Départs intermédiaires et mésoscopiques | 3 | 35–55 % | 35–55 % |
| Préfixe global et enveloppes presque sûres | 3 | 30–55 % | 30–55 % |
| Transport macroscopique et noyau signé relatif | 3 | 20–40 % | 20–40 % |
| Mélange des deux sources et horloges affines | 5 | 5–15 % | 5–15 % |

## Reste à établir

Les corollaires 5.2,5.3 et5.5 demandent encore leurs objets précis : vrai champ de signes indépendants et comparaison triangulaire ; tirage uniforme de dictionnaires avec ses comptes moyens et Markov ; dictionnaire{a,−a}, identitéΩ=Θ et cible du compte agrégé. La construction explicite ne démontre pas que « la plupart » des dictionnaires conviennent.

Restent ensuite les marques exactes signées et leur comparaison agrégée, les niveaux croissants, les queues et la limite Poisson–Gauss. La loi d’un dictionnaire à longueur unique ne fournit pas automatiquement ces conclusions. Aucun crédit nouveau n’est donné aux chapitres 6–7 ni au compagnon.

Les obligations antérieures restent visibles : relèvement produit général du lemme 6.1, conditionnement sharp, trajectoires, presque sûr, frontière microscopique et mélange de deux sources ; toutα>0 de3.19, taux précis exp(O(logM/loglogM)) de3.13/3.14/A.2, raffinements3.17/3.18, Fourier arbitraire et rang cyclomatique.

## Provenance et validation

Base du lot 11 : `89fc443af53ff7c3296a6c91203bf3d59f7605e8`. Cœur historique, PDF anglais et versions inchangés : Lean 4.32.0, mathlib v4.32.0, révision `81a5d257c8e410db227a6665ed08f64fea08e997`. Les identités figurent dans le [manifeste](../PaperCV282/source_manifest.json).

Les relectures portent sur les preuves et leur correspondance au papier. La compilation globale, l’audit exhaustif, le commit publié et les contrôles distants sont consignés séparément avec leurs empreintes. Les 17 contrôles réussis du lot 11 ne sont pas attribués au nouveau commit. Aucune nouvelle qualification Palomar n’est annoncée.
