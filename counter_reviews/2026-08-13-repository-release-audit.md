> **Provenance.** Report supplied by the repository owner on 2026-08-13.
> The supplied text does not encode the author/model or the exact prompt. It is
> therefore recorded as an agent-generated repository/release audit, not
> independent human peer review. Original SHA-256:
> `559467cac93acd16b471110b948d21e6d6460d4efc52536f213202bf36486246`.
> Scope: Paper C v09 artifacts, `paper-c-lean` PR #5, CI, Comparator and release
> qualification.

## Verdict

**Je ne recommande pas la séquence “merge de la PR #5, puis publication immédiate de la v09”.**

La PR est une **bonne préparation documentaire de la v0.48.1**, mais elle ne constitue pas encore un paquet de publication pleinement qualifié. Plus précisément :

| DécisionVerdict                                                                   |                                                                                               |
| --------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------- |
| Merger la PR telle quelle maintenant                                              | **NO-GO temporaire**                                                                          |
| Publier la v09 comme prépublication explicitement conditionnelle                  | **GO après les corrections ci-dessous**                                                       |
| Présenter la v09 comme un résultat inconditionnel intégralement certifié par Lean | **NO-GO en l’état**                                                                           |
| Rendre le dépôt public                                                            | Déjà fait, et globalement bénéfique, sous réserve de corriger quelques formulations publiques |

Le principal problème n’est pas le noyau Lean lui-même. Il se situe à la frontière entre le manuscrit, les propositions externes invoquées et ce que la formalisation certifie réellement.

## 1. Bloquant scientifique : le pont Halter–Koch n’est pas fermé

Le dépôt reconnaît explicitement que le théorème 1.1 est énoncé **sans condition dans le manuscrit**, alors que la cible Comparator prouve sa conclusion à partir de quatre propositions externes ordinaires. Parmi ces quatre propositions, la traduction de Halter–Koch vers le record Lean requis n’a pas été établie.

Le rapport `HK13-QO-conductor-fibres.md` est particulièrement clair :

- accès seulement partiel à la source primaire ;
- statut `agent_checked_with_open_gap` ;
- construction manquante de (K=\mathbf Q(\sqrt D)), de l’extension des idéaux, des classes d’unités liées au conducteur et de la descente vers les idéaux principaux de (\mathbf Z[\sqrt D]) ;
- conclusion explicite que les affirmations publiques doivent continuer à présenter le théorème 1.1 comme conditionnel tant que cette construction n’est pas fournie et vérifiée.

Cela ne démontre pas que le théorème est faux. Deux situations restent possibles :

1. le résultat de Halter–Koch permet effectivement de fermer le raisonnement, mais la construction détaillée n’a pas encore été écrite ;
2. le record Lean est sensiblement plus fort et plus global que ce dont le papier a réellement besoin, de sorte que l’écart serait principalement un problème d’interface de formalisation.

Mais, dans l’état actuel, un lecteur externe ne peut pas déterminer laquelle de ces deux interprétations est correcte. Or la PR ne modifie pas les pages mathématiques : elle remplace les PDF pour corriger leur texte de disponibilité et met à jour les métadonnées. Elle ne ferme donc pas cette obligation scientifique.

### Conséquence pour la v09

Pour conserver un énoncé inconditionnel, il faudrait isoler la proposition minimale réellement utilisée dans le lemme 9.2, puis fournir une dérivation détaillée depuis les résultats de Halter–Koch. Cette dérivation pourrait prendre la forme :

- d’un nouvel appendice mathématique dans le papier ;
- d’un certificat bibliographique positif beaucoup plus détaillé ;
- idéalement, d’une construction Lean du pont ou d’un remplacement du record actuel par une interface exactement alignée sur le lemme du manuscrit.

L’autre option honnête consiste à rendre explicitement conditionnels le théorème 1.1 et les autres résultats qui consomment ce pont. Le statut du dépôt indique que la dépendance se propage également à plusieurs résultats associés, notamment les théorèmes 1.2 et 1.4.

## 2. Bloquant de merge : la CI de la tête exacte de la PR est rouge

Le workflow associé au commit exact `a9e1bf8a02f21fe5470263ca6ebaa07a5fdc6e10` est actuellement en échec.

Le détail est cependant rassurant sur le plan mathématique :

- le job principal d’audit réussit ;
- les vérifications des octets PDF, du digest des sources, des certificats bibliographiques et de l’hygiène Lean réussissent ;
- le projet, les deux Challenges et les deux Solutions compilent ;
- l’audit exhaustif du noyau et de la liste d’axiomes réussit ;
- la cible de transfert infini–fini réussit ;
- seule la cible Comparator `theorem-one-one` échoue, pendant l’installation de la toolchain Lean, avant toute exécution du Comparator ou de la preuve.

Je considère donc cet échec comme **probablement infrastructurel**, pas comme une régression mathématique. Néanmoins, un paquet destiné à être publié ne devrait pas partir avec un badge rouge et sans résultat Comparator pour sa cible principale.

Il faut relancer la CI sur cette tête exacte et obtenir les trois jobs verts avant le merge. La PR est par ailleurs toujours marquée comme brouillon.

## 3. Un simple merge ne crée pas une version publique qualifiée

La PR indique elle-même qu’elle ne crée volontairement ni tag, ni release GitHub, ni dépôt Zenodo, ni nouvelle version Cambridge.

Actuellement, le dépôt ne contient que les tags :

- `v0.48.0` ;
- `v0.48.0-rc2` ;
- `v0.48.0-rc1` ;
- `v0.47.0`.

Il n’existe pas encore de tag `v0.48.1`. La seule release finale disponible est la `v0.48.0`, avec ses anciens PDF, archives et preuves durcies.

Après un simple merge, le lecteur aurait donc :

- une branche `main` décrivant une v0.48.1 ;
- aucun paquet `paper_c_lean_v0481.zip` publié ;
- aucune release GitHub correspondante ;
- aucun DOI de version Zenodo liant les nouveaux PDF et le dépôt exact ;
- aucune archive qualifiée regroupant les nouveaux PDF, les sources et les métadonnées.

La publication devrait porter sur un commit précis, accompagné au minimum d’un tag `v0.48.1`, de l’archive annoncée, de ses empreintes et d’un DOI Zenodo de version.

## 4. Les nouveaux PDF ne sont pas liés par la preuve Comparator durcie

La PR et les documents de reproductibilité sont honnêtes sur ce point : la preuve durcie publiée avec la v0.48.0 certifie le fileset Comparator inchangé et les anciennes empreintes PDF, mais **ne lie pas les nouveaux octets PDF de la v0.48.1**.

Cela ne remet pas en cause le calcul Lean, puisque les sources Lean et Comparator sont inchangées. En revanche, cela empêche de présenter la v0.48.1 comme un triplet indivisible « nouveaux manuscrits — sources — preuve Comparator » bénéficiant du même niveau de qualification que la v0.48.0.

Une nouvelle exécution durcie serait donc souhaitable, non pour retester une modification mathématique inexistante, mais pour produire une chaîne de provenance unique liant :

- le commit final v0.48.1 ;
- les deux nouvelles empreintes PDF ;
- le fileset Comparator inchangé ;
- les versions de Lean, Mathlib, Comparator, lean4export et landrun ;
- les deux résultats Comparator.

Attention également au workflow : les PR et pushes autorisent explicitement un fallback Comparator non sandboxé et non certifiant. Le mode réellement durci n’est imposé que lors d’un lancement manuel avec `require_hardened=true`. Un simple push de tag ne déclenche donc pas automatiquement la qualification stricte.

Je recommande soit un workflow séparé `release-qualification`, sans aucun fallback, soit une procédure locale durcie dont l’archive de résultat est ensuite publiée et liée cryptographiquement à la release.

## 5. Les textes détaillés du dépôt sont bons, mais la description publique sur-vend encore le résultat

Le `README` est globalement très transparent :

- il annonce sept propositions externes encore ouvertes ;
- il précise que les fichiers Challenge contiennent chacun un `by sorry` intentionnel ;
- il indique que le `sorry_count = 0` concerne le côté preuve et le cœur gelé ;
- il précise que le dépôt ne certifie pas à lui seul l’intégralité des 71 pages du manuscrit ;
- il expose le décalage entre le théorème 1.1 du papier et la cible Comparator conditionnelle.

En revanche, la description courte affichée par GitHub annonce actuellement :

> « 4070 declarations, zero sorry, exhaustive kernel axiom audit, byte-hashed certified PDFs »

Cette formulation est trop absolue :

- il existe bien deux `sorry` intentionnels dans les Challenges ;
- les nouveaux PDF v0.48.1 sont hachés, mais pas liés par la preuve durcie publiée ;
- l’audit exhaustif porte sur le noyau formalisé, pas sur la totalité du manuscrit ni sur les sept propositions externes.

Une description plus sûre serait, par exemple :

> Lean 4 formalization accompanying Paper C — 4,070 audited public declarations; zero sorry in the frozen core and Solution files; seven explicit external literature bridges; byte-hashed manuscripts and reproducible kernel audit.

Le DOI affiché dans la description GitHub est également `10.5281/zenodo.21735482`, alors que le README présente `10.5281/zenodo.21735481` comme DOI conceptuel de la formalisation. Ce n’est pas nécessairement incohérent si le premier est un DOI de version v0.48.0, mais il faut alors l’indiquer explicitement et le remplacer ou le compléter lors de la publication de la v0.48.1.

## 6. La mention de deux contre-revues « indépendantes » doit être qualifiée

Le corps de la PR annonce « two independent read-only counter-reviews — GO », alors qu’aucune review GitHub n’est enregistrée sur la PR.

Ces deux contre-revues ont peut-être réellement été réalisées hors de GitHub, mais le terme « independent » peut être interprété comme une validation externe ou humaine, tandis que les métadonnées du dépôt indiquent correctement un statut `agent-reviewed` et l’absence de revue humaine indépendante.

Il faudrait donc soit :

- publier les deux rapports avec leurs auteurs ou modèles, dates, prompts, périmètres et empreintes ;
- écrire « two independent agent counter-reviews » ;
- ou supprimer cette ligne du résumé de validation.

Ce point n’est pas un blocage scientifique en lui-même, mais il est important pour ne pas affaiblir la crédibilité du reste de la chaîne d’audit.

## 7. Le contrôle visuel des PDF reste à rendre reproductible

La PR affirme que seules les pages anglaises 68–69 et françaises 70–71 ont changé visuellement, que toutes les polices sont incorporées et qu’il n’existe ni erreur LaTeX, ni référence non résolue, ni URI locale ou privée.

Le workflow actuel vérifie les empreintes des PDF, mais ne démontre pas automatiquement ces propriétés visuelles et éditoriales. Un rapport de release devrait conserver :

- `qpdf --check` ou équivalent ;
- l’inventaire des polices incorporées ;
- l’extraction des hyperliens et métadonnées PDF ;
- un diff pixel ou perceptuel contre la v0.48.0 ;
- une recherche de chemins locaux, URI privées et références au dépôt d’intégration ;
- quelques captures des pages réellement modifiées.

Je n’ai pas pu rendre directement les deux PDF de la tête de PR dans cette session. Ma vérification de leur contenu est donc limitée à leurs identités Git, leurs empreintes, les métadonnées du dépôt et le périmètre déclaré de la modification. Je ne certifie pas indépendamment ici la typographie, les liens ou les pages 68–69/70–71.

## Points positifs

La PR elle-même est propre et bien circonscrite : dix fichiers sont modifiés, aucun fichier du cœur Lean ni aucune configuration Comparator ne change. Les modifications portent sur les deux PDF, les métadonnées, les documents de statut, la reproductibilité et le numéro de version.

Le job d’audit principal montre également que :

- les nouveaux octets PDF correspondent aux empreintes déclarées ;
- le digest du cœur Lean est intact ;
- les certificats bibliographiques sont cohérents avec le registre ;
- les quatre racines Challenge/Solution compilent séparément ;
- l’audit du noyau et de l’allowlist des axiomes réussit.

Le dépôt public est donc un **excellent artefact d’audit**, à condition de ne pas le présenter comme une preuve inconditionnelle des résultats dont les ponts externes demeurent ouverts.

## Séquence minimale recommandée avant publication

1. **Traiter le point Halter–Koch.** Soit fermer la dérivation exacte utilisée par le papier, soit rendre explicitement conditionnels les résultats concernés. C’est le seul véritable bloqueur scientifique.
2. **Corriger les formulations publiques.** Modifier la description courte du dépôt, qualifier les deux contre-revues comme revues par agents et distinguer clairement DOI conceptuel et DOI de version.
3. **Relancer la CI sur la tête finale.** Les trois jobs doivent être verts. L’échec actuel paraît incidentel, mais ne doit pas rester dans l’historique de qualification final.
4. **Produire une preuve durcie v0.48.1.** Elle doit lier le commit final et les deux nouvelles empreintes PDF, sans fallback non certifiant.
5. **Conserver un rapport QA des PDF.** Il doit confirmer de manière reproductible les polices, les liens, l’absence de chemins privés et le diff limité aux pages annoncées.
6. **Merger, puis figer la livraison.** Créer le tag `v0.48.1`, la release GitHub, `paper_c_lean_v0481.zip`, son SHA‑256, les logs d’audit et l’archive Comparator publique.
7. **Publier la version Zenodo de la formalisation avant la v09 du papier.** Le papier pourra alors citer le DOI conceptuel et le DOI exact de version correspondant aux octets publiés.

### Conclusion

**La PR mérite d’être conservée et probablement mergée après une CI verte, mais son merge ne suffit pas à rendre la v09 publiable comme résultat inconditionnel formellement certifié.**

Le point décisif est le pont Halter–Koch. Une fois ce point fermé — ou correctement transformé en hypothèse explicite — et la release v0.48.1 qualifiée, le dépôt public constituera un support particulièrement solide et transparent pour la publication de la v09.