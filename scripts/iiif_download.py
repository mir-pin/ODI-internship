import os
import json
import csv
import requests
import re

MANIFEST_URL = "https://collections.library.yale.edu/manifests/10991686"
OUTPUT_DIR = "cards_images"

os.makedirs(OUTPUT_DIR, exist_ok=True)

# --- Load manifest ---
manifest = requests.get(MANIFEST_URL).json()

# Save full manifest
with open(os.path.join(OUTPUT_DIR, "manifest.json"), "w", encoding="utf-8") as f:
    json.dump(manifest, f, indent=2, ensure_ascii=False)

print("Manifest saved")


# --- Helper to extract text ---
def get_text(field):
    if isinstance(field, dict):
        return " ".join(v for values in field.values() for v in values)
    return field if field else ""


# --- Build deck metadata ---
deck_metadata = {}

for item in manifest.get("metadata", []):
    key = get_text(item.get("label")).strip()
    value = get_text(item.get("value")).strip()
    deck_metadata[key] = value

# Add a few useful extras
deck_metadata["title"] = get_text(manifest.get("label"))
deck_metadata["manifest_id"] = manifest.get("@id") or MANIFEST_URL

# --- SAVE TO CSV ---
csv_path = os.path.join(OUTPUT_DIR, "deck_metadata.csv")

with open(csv_path, "w", newline="", encoding="utf-8") as f:
    writer = csv.writer(f)

    # header row
    writer.writerow(deck_metadata.keys())

    # values row
    writer.writerow(deck_metadata.values())

print("Deck metadata CSV saved")

# --- Iterate canvases ---
canvases = manifest.get("items", [])

for i, canvas in enumerate(canvases):
    try:
        # --- Label ---
        label = get_text(canvas.get("label", {}))
        if not label:
            label = f"image_{i+1}"

        # --- Clean label ---
        safe_label = re.sub(r'[^a-zA-Z0-9_-]', '_', label)

        # --- Build filename ---
        filename_base = f"{i+1:03}_{safe_label}"

        # --- Get IIIF image url ---
        annotation_page = canvas["items"][0]
        annotation = annotation_page["items"][0]
        image_url = annotation["body"]["id"]

        print(f"Downloading: {image_url}")

        # --- Download image ---
        img_response = requests.get(image_url)

        # Check response
        if img_response.status_code != 200:
            print(f"Failed ({img_response.status_code})")
            continue

        content_type = img_response.headers.get("Content-Type", "")
        if "image" not in content_type:
            print(f"Not an image (got {content_type})")
            continue

        # --- Save image ---
        image_path = os.path.join(OUTPUT_DIR, f"{filename_base}.jpg")
        with open(image_path, "wb") as f:
            f.write(img_response.content)

        print(f"Saved {filename_base}.jpg")

    except Exception as e:
        print(f"Error with canvas {i+1}: {e}")

print("Done!")

