# Scripts Directory

This directory contains utility scripts used in the ODI/BACODI project.

## Setup

1. **Install Dependencies**:
   Ensure you have Python installed, then run from the root directory:
   ```bash
   pip install -r scripts/requirements.txt
   ```

## Directory Summary

### IIIF Image Downloader (Yale Digital Collections)

**`iiif_download.py`** is a Python script to download images and metadata from a IIIF manifest, specifically tested with Yale University Library Digital Collections.

The script:

1. Loads a IIIF manifest
2. Extracts **deck-level metadata**
3. Iterates through canvases (images)
4. Retrieves image URLs via the IIIF Image API
5. Downloads and saves images locally
