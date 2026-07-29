# Checklist de release v1.0.0 / v1.0.0 release checklist

## Effectué par le commit de préparation / Completed by the preparation commit

- Version, métadonnées de citation, changelog et notes de release.
- Documentation de portée, contrat d'API, build, garde et arbre propre.

## À effectuer manuellement après validation / Manual work after validation

- Pousser le commit final et vérifier la CI distante.
- Créer puis pousser le tag annoté `v1.0.0`.
- Créer et publier la release GitHub, en collant `RELEASE_NOTES_v1.0.0.md`.
- Vérifier le traitement par Zenodo, relever le DOI de version et le DOI
  conceptuel, vérifier licence et auteurs.
- Ajouter ensuite uniquement les DOI vérifiés à la documentation, sans
  modifier rétroactivement un tag publié.
