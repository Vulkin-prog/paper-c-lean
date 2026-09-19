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
