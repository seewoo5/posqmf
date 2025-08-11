#!/bin/bash

# Define the source and destination directories
SOURCE_DIR="./posqmf/sage"
DEST_DIR="./posqmf"
INIT_FILE="$DEST_DIR/__init__.py"

# Check if the source directory exists
if [[ ! -d $SOURCE_DIR ]]; then
  echo "Error: Source directory $SOURCE_DIR does not exist."
  exit 1
fi

# Remove existing __init__.py if it exists, and create a new one
if [[ -f $INIT_FILE ]]; then
  rm "$INIT_FILE"
  echo "Removed existing $INIT_FILE."
fi
touch "$INIT_FILE"
echo "from __future__ import absolute_import\n" > "$INIT_FILE"
echo "Created new $INIT_FILE with absolute import statement."

# Loop over all .sage files in the source directory
for file in "$SOURCE_DIR"/*.sage; do
  # Check if there are any .sage files
  if [[ ! -e $file ]]; then
    echo "No .sage files found in $SOURCE_DIR."
    break
  fi

  # Run sage --preparse on the file
  sage --preparse "$file"

  # Get the output file name (sage prepends an extra `.py` to the file name)
  output_file="${file%.sage}.sage.py"

  # Define the new file name with .py extension
  new_name="$DEST_DIR/$(basename "${file%.sage}.py")"

  # Move the resulting file to the destination directory with the new name
  if [[ -e $output_file ]]; then
    mv "$output_file" "$new_name"
    echo "Processed and moved $output_file to $new_name."

    # Extract the base name (without extension) for the import
    base_name=$(basename "$new_name" .py)

    # Append the import statement to __init__.py
    echo "from .$base_name import *" >> "$INIT_FILE"
    echo "Added import for $base_name to $INIT_FILE."
  else
    echo "Error: Expected output file $output_file not found."
  fi
done
