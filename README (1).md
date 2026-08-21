# GeoExif Meuse 55

**Carnet de terrain naturaliste** pour Windows — photos géolocalisées, observations sans photo, indices, carte, multi-sorties, import audio (BirdNET Live / Birda / Chirpity), briefs IA, archive & recovery.

> Projet personnel orienté **Meuse (55) / Grand Est**.  
> Ce n’est **pas** un produit commercial : c’est un outil de terrain développé pour un usage réel (affût, billebaude, écoutes).

**Version actuelle :** 4.0.17  
**Auteur :** Wilmet Sébastien

---

## À quoi ça sert ?

| Besoin terrain | GeoExif |
|----------------|---------|
| Ne plus perdre ses repérages | Carte + notes + GPS + météo |
| Annoter photos (RAW/JPEG) + vidéos | Carnet par sortie, métadonnées ExifTool |
| Observer **sans** photo | Points manuels, indices, prises de son |
| Plusieurs sorties dans l’année | Projet Meuse, carte cumulée, briefs multi-périodes |
| Audio oiseaux / mammifères | Import BirdNET Live, Birda CLI, Chirpity |
| Disque externe hors-ligne | Archive locale, pack recovery ZIP, débrief texte |

---

## Prérequis

- **Windows 10 / 11**
- **Python 3.10+** (testé avec 3.10)
- **[ExifTool](https://exiftool.org/)** dans le `PATH` ou `exiftool.exe` à côté du script / dans `tools/`
- Connexion Internet pour la carte (tuiles OSM) et les options IA (clés API optionnelles)

### Dépendances Python

```bash
pip install -r requirements.txt
```

### Outils optionnels (audio)

| Outil | Usage |
|-------|--------|
| [BirdNET Live](https://birdnet.cornell.edu/) | Export session → import GeoExif |
| [Birda CLI](https://github.com/tphakala/birda) | Analyse audio → CSV → carnet |
| [Chirpity](https://github.com/Mattk70/Chirpity-Electron) | Export CSV → carnet |
| Audacity | Prétraitement du son |

---

## Installation rapide

```bash
git clone https://github.com/VOTRE_COMPTE/geoexif-meuse.git
cd geoexif-meuse
python -m venv .venv
.venv\Scripts\activate
pip install -r requirements.txt
python carnet_geoexif_v24.py
```

Au **premier démarrage**, un assistant propose : dossier photos, GPX, thème, clés IA, chemins audio.

---

## Lancer

```bash
python carnet_geoexif_v24.py
```

Raccourcis utiles (modifiables dans **Affichage → Raccourcis clavier** ou **F1**) :

| Raccourci | Action |
|-----------|--------|
| `Ctrl+S` | Enregistrer l’observation |
| `Ctrl+←` / `Ctrl+→` | Obs. précédente / suivante |
| `Ctrl+O` | Ouvrir un dossier sortie |
| `Ctrl+I` | Import son |
| `F2` | Brief IA |
| `F11` | Plein écran |

---

## Structure utile

```
geoexif-meuse/
├── carnet_geoexif_v24.py   # application
├── requirements.txt
├── README.md
├── LICENSE
├── .gitignore
├── TUTORIEL_GeoExif_4.0.md
├── MODE_EMPLOI_GeoExif.md
└── docs…                   # notices / guides
```

Les **données utilisateur** (config, sorties connues, archives) sont stockées dans un dossier données local Windows — **pas** dans le dépôt Git.

---

## Ce que vous ne devez PAS committer

- `app_config.json` (chemins, clés API)
- `observations.json` / notes de terrain
- GPS de spots sensibles, photos, enregistrements
- Fichiers `.env`, backups personnels

→ Voir `.gitignore`.

---

## Fonctions principales (v4)

- Dossier sortie → GPX → synchro horloge (été −1 h / hiver −2 h) → annotations
- Observations sans photo, indices, affût / série GPS+heure
- Carte (filtres, mesure distance, point d’écoute)
- Multi-sorties : carte cumulée, projet, analyses
- Import son unifié (BirdNET Live, Birda, Chirpity)
- Briefs IA (sortie / multi / archive hors-ligne)
- Sauvegardes versionnées, pack recovery ZIP
- Thèmes sombre / clair / papier

---

## Licence

MIT — voir [LICENSE](LICENSE).  
Usage libre ; aucune garantie. Les données de terrain restent **votre** responsabilité (ne publiez pas de spots sensibles).

Calendriers de chasse / espèces : **indicatifs** uniquement — vérifier les sources officielles (fédération, arrêtés préfectoraux).

---

## Avertissement

Logiciel de passionné, évolutif, testé sur un workflow Windows réel.  
Issues et suggestions bienvenues, **sans engagement de support** type éditeur logiciel.

---

*GeoExif Meuse 55 — carnet naturaliste, pas une usine à gaz.*
