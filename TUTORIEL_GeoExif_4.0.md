# Tutoriel GeoExif 4.0 — Meuse 55

**Version logicielle :** 4.0.0  
**Auteur :** Wilmet Sébastien  
**Public :** naturaliste / photographe de terrain (département de la Meuse)

Ce guide décrit l’usage **complet** du logiciel, cas par cas.  
Principe directeur : **GeoExif = carnet + GPS + synthèse**. Les photos vivent sur Amazon ; le son passe par Birda ; les cartes lourdes (QGIS) restent optionnelles.

---

## Sommaire

1. [Installation et premier démarrage](#chapitre-1--installation-et-premier-démarrage)
2. [L’interface en 5 minutes](#chapitre-2--linterface-en-5-minutes)
3. [Scénario A — Sortie photo classique](#chapitre-3--scénario-a--sortie-photo-classique)
4. [Scénario B — Affût / série sans GPS précis](#chapitre-4--scénario-b--affût--série-sans-gps-précis)
5. [Scénario C — Observation sans photo](#chapitre-5--scénario-c--observation-sans-photo)
6. [Scénario D — Indices (terrier, empreinte, coulée)](#chapitre-6--scénario-d--indices)
7. [Scénario E — Prise de son et Birda](#chapitre-7--scénario-e--prise-de-son-et-birda)
8. [Scénario F — Plusieurs sorties, bilan semaine / mois / année](#chapitre-8--scénario-f--bilans-multi-sorties)
9. [Scénario G — Disque externe absent (hors-ligne)](#chapitre-9--scénario-g--hors-ligne-et-récupération)
10. [Scénario H — Caméras et enregistreurs](#chapitre-10--scénario-h--caméras-et-enregistreurs)
11. [Carte, mesures, exports](#chapitre-11--carte-mesures-exports)
12. [Sauvegardes et pack recovery](#chapitre-12--sauvegardes-et-pack-recovery)
13. [Espace de travail multi-écran](#chapitre-13--espace-de-travail-multi-écran)
14. [IA (identification photo et briefs)](#chapitre-14--ia)
15. [Checklist terrain → soirée](#chapitre-15--checklist)
16. [FAQ courte](#chapitre-16--faq-courte)

---

## Chapitre 1 — Installation et premier démarrage

### 1.1 Prérequis

- Windows 10 / 11  
- **ExifTool** (`exiftool.exe`) : à côté de GeoExif, ou dans le PATH  
- Python uniquement si vous lancez le `.py` (sinon version compilée `.exe` si vous en avez une)  
- Connexion Internet : météo, géocodage lieu, IA (optionnel)

### 1.2 Premier lancement

Au premier démarrage, un **assistant de configuration** peut s’ouvrir :

1. Dossier photos par défaut (disque externe ou local)  
2. Dossier des traces GPX (optionnel)  
3. Thème (sombre / clair / papier)  
4. Clés IA (Gemini et/ou xAI) — optionnel  
5. Dossier cloud (Drive / Dropbox…) — optionnel  

Vous pouvez rouvrir cet assistant : **Sauvegardes → Configuration…**

### 1.3 Où sont les données ?

| Élément | Emplacement typique |
|--------|----------------------|
| Config, archive, sorties connues | `%LOCALAPPDATA%\GeoExif\` |
| Photos | Votre disque / Amazon Photos |
| Carnet d’une sortie | `observations.json` **dans** le dossier de la sortie |
| Archive hors-ligne | `%LOCALAPPDATA%\GeoExif\archive_carnets\` |

**Important :** les versions du logiciel ne doivent plus « perdre » les sorties : la liste vit dans AppData, pas uniquement à côté du `.py`.

---

## Chapitre 2 — L’interface en 5 minutes

### 2.1 Menus

| Menu | Rôle |
|------|------|
| **Fichier** | Ouvrir sortie, GPX, import/export terrain |
| **GPS** | Synchroniser, décalages été/hiver, lot, affût/série |
| **Carnet** | Enregistrer, sans photo, brief, indices, **Birda** |
| **Carte** | Cumulée, placer obs., mesure, capture |
| **Outils** | Projet, analyses, exports, caméras, cloud |
| **Sauvegardes** | Config, archive, recovery ZIP, cache |
| **Affichage** | Thèmes, barre latérale, plein écran, **espace de travail** |
| **Aide** | FAQ, à propos |

### 2.2 Deux modes

- **Mode Sortie** : terrain du jour (dossier, GPS, carnet)  
- **Mode Saison** : projet, carte cumulée, analyses  

### 2.3 Onglets principaux

- **Carte** : points GPS, filtres, trace GPX, placer une observation  
- **Carnet** : liste médias + fiche observation + météo  

### 2.4 Barre d’icônes

Raccourcis : ouvrir dossier, GPX, synchro, décalages été/hiver, brief, carte cumulée, mesure, etc.  
Survolez une icône pour l’infobulle.

---

## Chapitre 3 — Scénario A — Sortie photo classique

**Cas :** vous revenez d’une billebaude, carte SD pleine, trace GPX sur le téléphone (OsmAnd / Locus).

### Étape 1 — Copier les photos

1. Importez les RAW/JPEG (FastStone, explorateur Windows…) dans un dossier du type :  
   `2026-07-19_Bois_de_XXX`  
2. (Optionnel) Les mêmes images partent vers **Amazon Photos** (classement **par jour**).

### Étape 2 — Ouvrir la sortie

1. **Fichier → Ouvrir dossier photos / sortie**  
2. GeoExif enregistre cette sortie dans la liste des sorties connues.

### Étape 3 — Charger le GPX

1. **Fichier → Charger une trace GPX…**  
2. Ou icône satellite / GPX dans la barre.

### Étape 4 — Décalage horaire (souvent obligatoire)

Les appareils et le GPS ne sont pas toujours sur le même fuseau.

- **GPS → Décalage été (−1 h)** ou **Hiver (−2 h)**  
  (valeurs que vous utilisez pour caler photos et trace)

### Étape 5 — Synchroniser

1. **GPS → Synchroniser photos & GPX**  
2. Attendez la fin (barre de progression).  
3. Les points apparaissent sur la **Carte**.

En cas d’erreur de calage : **Annuler dernière synchro**, ajuster le décalage, resynchroniser.

### Étape 6 — Annoter dans le carnet

1. Onglet **Carnet**  
2. Sélectionnez une photo (ou une vidéo 🎬)  
3. Renseignez : catégorie, espèce, nombre, comportement, certitude, type d’indice, lieu, notes  
4. **Repère Amazon (jour)** : bouton **Jour auto** → ex. `19 juillet 2026` → **Sauver**  
5. **Enregistrer l’observation** (ou `Ctrl+S`)

### Étape 7 — Brief de la sortie

1. **Carnet → Brief IA de la sortie**  
2. Copiez le texte vers Gemini / ChatGPT / Grok  
3. Ou exportez PDF / Word si proposé  

### Étape 8 — Sécuriser

1. **Sauvegardes → Copier sorties accessibles → archive PC** (disque encore branché)  
2. De temps en temps : **Pack recovery ZIP…**

---

## Chapitre 4 — Scénario B — Affût / série sans GPS précis

**Cas :** série de photos au même endroit, sans point GPS fiable sur chaque fichier, avec une plage horaire approximative.

1. Ouvrez le dossier de la sortie  
2. Dans le carnet, **sélectionnez le groupe** de photos de l’affût  
3. **GPS → Affût / série (GPS + horaires)…**  
4. Indiquez :
   - un **point GPS commun** (carte ou lat/lon)
   - la **date** et la **tranche horaire** (début / fin)
   - répartition des heures ou heure identique  
5. Validez : écriture des métadonnées (suivez la barre de progression)

Ensuite, annotez comme au scénario A (espèce, notes…).

---

## Chapitre 5 — Scénario C — Observation sans photo

**Cas :** animal vu ou entendu, pas de photo (ou photo impossible).

### Variante 1 — Depuis le carnet

1. **Carnet → Observation sans photo…**  
2. Ou bouton dédié / mode **Placer observation** sur la carte  
3. Cliquez la carte à l’endroit voulu (icône d’une autre couleur)  
4. Remplissez la fiche → **Enregistrer**

### Variante 2 — Carnet sans aucune photo

1. **Fichier → Carnet sans photos…**  
2. Créez / ouvrez un dossier « carnet seul »  
3. Ajoutez des observations manuelles toute la sortie  

Ces points comptent dans les briefs, la carte cumulée et l’archive.

---

## Chapitre 6 — Scénario D — Indices

**Cas :** terrier, empreinte, coulée, latrines, frottis…

1. Photo de l’indice **ou** observation sans photo  
2. Dans la fiche :
   - **Type d’indice** : Empreinte, Terrier, Coulée, etc.  
   - Espèce probable + **certitude** (Sûr / Probable / Possible)  
3. Sur la carte, les indices ont des **formes différentes** des contacts directs  

### Dossier d’indices + import

**Carnet → Indices — dossier + import…**  
Utile pour regrouper des photos d’indices et les intégrer au carnet.

### Rappels (ne pas oublier un terrier en mars)

1. Renseignez une **date de rappel** sur la fiche si le champ est présent  
2. **Carnet → Rappels indices / suivi…**  
3. Consultez la liste des rappels à venir  

---

## Chapitre 7 — Scénario E — Prise de son et Birda

**Cas :** enregistrement d’un chant / de la nuit, analyse dans **Birda GUI**, résultat dans GeoExif.

GeoExif **n’analyse pas** le son. Birda le fait ; GeoExif **importe** le résultat.

### Workflow recommandé

1. Ouvrez la **sortie** du jour dans GeoExif  
2. **Carnet → Birda — prise de son & import…**  
3. (Optionnel) **Ouvrir Audacity** → nettoyer → exporter WAV  
4. **Ouvrir Birda GUI** → analyser le fichier  
5. Une fois : choisissez le **dossier des résultats** Birda (mémorisé)  
6. **Importer le dernier résultat (semi-auto)** → confirmez le fichier proposé  
   - ou **Choisir un fichier JSON/CSV…** à la main  
7. Les espèces arrivent en observations **Prise de son (Birda)**  
8. Vérifiez noms / certitudes, complétez le lieu si besoin  

### Observation manuelle « entendu »

Sans fichier Birda : type d’indice **Entendu / Chant** ou **Prise de son (Birda)**, saisie à la main.

---

## Chapitre 8 — Scénario F — Bilans multi-sorties

**Cas :** brief de la semaine, du mois, de la saison.

1. **Outils → Brief multi-sorties…**  
2. Filtrez : 7 jours, 30 jours, mois, année, plage perso  
3. Cochez les sorties  
4. **Brief IA** (texte à coller dans une IA)  
   ou export **PDF** / **Word**

### Débrief 100 % texte sans photos

**Outils → Débrief texte (archive, sans photos)…**  

- Lit l’**archive PC** uniquement  
- Idéal disque débranché, photos seulement sur Amazon  
- Inclut notes, météo, espèces, indices  

### Carte cumulée

**Carte → Carte cumulée…**  

- Toutes les sorties / par sortie / par espèce / masquer  
- Clic sur une sortie de la liste pour la retrouver / l’éditer (si proposé)

### Projet Meuse / saison

**Outils → Projet Meuse / saison…**  
Regroupe les sorties de l’année, analyses d’effort et de richesse.

---

## Chapitre 9 — Scénario G — Hors-ligne et récupération

### Photos sur Amazon, carnets sur le PC

Vous n’avez besoin que des **JSON / KML / archive**, pas des RAW locaux, pour :

- carte cumulée (points déjà en carnet)  
- fiches espèces (si enrichies / archivées)  
- débrief texte  

### Disque ancien → nouveau

1. Branchez l’ancien disque  
2. **Sauvegardes → Rescanner mes sorties…**  
3. **Copier sorties accessibles → archive PC**  
4. **Pack recovery ZIP** (copie de secours)  
5. Débranchez l’ancien disque  

Sans disque, l’archive AppData conserve les observations.

### Pack recovery ZIP

**Sauvegardes → Pack recovery ZIP…**  

Contient : archive_carnets, sorties connues, config…  
**Pas les photos** (volontaire).  
À mettre sur clé USB ou cloud.

---

## Chapitre 10 — Scénario H — Caméras et enregistreurs

1. **Outils → Caméras & enregistreurs…**  
2. Ajoutez un dispositif : type, nom, date de pose, délai de relève (ex. 3–4 jours), piles si besoin  
3. **Poser un dispositif sur la carte** pour le GPS  
4. Consultez les statuts (à relever, en retard…)  

Utile pour ne pas oublier une camera trap en forêt.

---

## Chapitre 11 — Carte, mesures, exports

### Carte de la sortie

- Filtres par catégorie  
- Trace GPX (case à cocher)  
- **Placer observation**  
- Formes d’indices vs contacts  

### Mesure

**Carte → Mesure distance (km)**  
Deux clics → segment + distance ; recliquer pour effacer.

### Exports utiles

| Export | Usage |
|--------|--------|
| KML / KMZ | Google Earth |
| GeoJSON | QGIS |
| CSV | tableur / sciences participatives |
| PDF du jour | compte-rendu simple |

**Outils →** les commandes d’export correspondantes.

### QGIS (optionnel, hors GeoExif)

1. Exporter GeoJSON  
2. Ouvrir dans QGIS + fond OSM/IGN  
3. Analyses avancées (habitats, 3D…) **en dehors** de GeoExif  

---

## Chapitre 12 — Sauvegardes et pack recovery

| Action | Quand |
|--------|--------|
| Enregistrement observation | Automatique dans `observations.json` |
| Miroir archive PC | À chaque sauvegarde de carnet + copie manuelle globale |
| Sauvegardes automatiques | **Sauvegardes → Sauvegardes automatiques…** |
| Pack recovery ZIP | Avant voyage, changement de PC, gros ménage |
| Cloud (Drive/Dropbox) | **Outils → Cloud…** si vous synchronisez un dossier |

**Gérer / retirer des sorties…** : retire une sortie de la liste (ex. séance drone sans faune) sans forcément tout effacer du disque.

---

## Chapitre 13 — Espace de travail multi-écran

Tk ne détache pas les onglets comme un navigateur. GeoExif propose :

1. **Affichage → Détacher la carte (2ᵉ écran)**  
2. Glisser la fenêtre carte sur le second moniteur  
3. Garder le **carnet** sur l’écran principal  
4. **Affichage → Enregistrer l’espace de travail**  

Au prochain démarrage, la disposition peut être **restaurée** automatiquement.

**Réattacher les fenêtres** ramène carte et journal dans la fenêtre principale.

---

## Chapitre 14 — IA

### Identification sur photo

1. Configurez une clé (**Gemini** et/ou **xAI**) dans la config IA  
2. Dans le carnet, photo sélectionnée → bouton **🤖**  
3. Vérifiez la proposition → appliquez → **Enregistrez**  

L’IA peut se tromper : la validation humaine reste obligatoire.

### Brief texte

- Une sortie : **Brief IA de la sortie**  
- Plusieurs : **Brief multi-sorties** ou **Débrief texte archive**  

Le brief est un **prompt** à coller dans l’IA de votre choix (carte décorative retirée volontairement).

---

## Chapitre 15 — Checklist

### Avant de partir

- [ ] Batteries, cartes, GPS / appli trace (OsmAnd, Locus…)  
- [ ] Heure de l’appareil photo à peu près juste  

### Au retour

- [ ] Copie photos → dossier du jour  
- [ ] (Option) Envoi Amazon Photos  
- [ ] Ouvrir dossier dans GeoExif  
- [ ] Charger GPX → décalage été/hiver → **Synchroniser**  
- [ ] Annoter les contacts importants  
- [ ] Affût/série si besoin  
- [ ] Indices + rappels  
- [ ] Birda si enregistrements  
- [ ] Brief si utile  
- [ ] Archive PC / recovery de temps en temps  

### Une fois par mois

- [ ] Pack recovery ZIP  
- [ ] Vérifier rappels indices / caméras  
- [ ] Brief mois (multi-sorties)  

---

## Chapitre 16 — FAQ courte

**Mes points sont décalés sur la carte**  
→ Décalage heure photo / GPX : presets été −1 h ou hiver −2 h, puis resynchro.

**ExifTool introuvable**  
→ Placez `exiftool.exe` à côté de GeoExif.

**Je ne vois plus les espèces sans le disque**  
→ **Copier sorties → archive PC** quand le disque est branché ; utilisez le débrief archive.

**Birda n’envoie rien tout seul**  
→ Normal : mode **semi-auto** (dernier fichier du dossier + votre confirmation).

**Amazon**  
→ Pas d’album obligatoire : **repère jour** (`19 juillet 2026`) via **Jour auto**.

**Changer pour PyQt ?**  
→ Non pour la 4.0 : refonte trop lourde. La base actuelle est volontairement conservée.

---

## Schéma récapitulatif du flux

```
Terrain
  ├─ Photos (+ vidéos)
  ├─ Trace GPX
  ├─ Notes / indices / sons
  └─ (Caméras posées)
        │
        ▼
Soirée PC
  ├─ Dossier photos → GeoExif
  ├─ GPX + synchro (+ décalage)
  ├─ Carnet (espèces, certitude, Amazon jour)
  ├─ Birda GUI → import semi-auto
  └─ Archive PC
        │
        ▼
Plus tard
  ├─ Carte cumulée / fiches espèces
  ├─ Brief semaine-mois-année
  ├─ Débrief texte hors-ligne
  ├─ Pack recovery ZIP
  └─ (QGIS si analyse poussée)
```

---

*Fin du tutoriel GeoExif 4.0 — bon terrain en Meuse.*
