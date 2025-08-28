#!/usr/bin/env python3
"""
media_metadata_editor.py
A GUI tool for Browse, editing and exporting media‑library metadata.

Author : Bill & Marv  •  May 2025
Python : 3.10+

FIXES APPLIED:
1. Added rating_key field to database schema
2. Fixed load_music_fields to properly handle rating_key
3. Fixed save_music_record to properly save rating_key
4. Added database migration for existing databases
"""

from __future__ import annotations
import json
import os
import sqlite3
import sys
import textwrap
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Tuple
import shutil
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from PIL import Image, ImageTk       # pip install pillow
import tempfile
import threading
import time
import shlex
import os
from datetime import datetime
import requests
import urllib.parse

# Plex integration constants
PLEX_TOKEN = "Aus8xGZEB6MusPMLsH51"
PLEX_SERVER_URL = "https://192-168-2-15.9c315f1de13144e6b7651c70c13bad0c.plex.direct:32400"

def open_with_default_app(path: str, app_instance=None) -> subprocess.Popen:
    """
    Launch *path* with the system-registered default application.
    If app_instance is provided and has current_video_process, kills it first.
    Returns the process object for tracking.
    """
    # Kill previous video process if we have an app instance with one
    if app_instance and hasattr(app_instance, 'current_video_process') and app_instance.current_video_process:
        try:
            app_instance.current_video_process.terminate()
            app_instance.current_video_process.wait(timeout=2)  # Wait up to 2 seconds
        except:
            try:
                app_instance.current_video_process.kill()  # Force kill if terminate fails
            except:
                pass
        app_instance.current_video_process = None
    
    # Launch new process
    if sys.platform.startswith("darwin"):          # macOS
        process = subprocess.Popen(["open", path])
    elif sys.platform.startswith(("win32", "cygwin")):  # Windows
        os.startfile(path)                         # type: ignore[attr-defined]
        process = None  # os.startfile doesn't return a process
    else:                                          # Linux / *BSD
        process = subprocess.Popen(["xdg-open", path])
    
    return process

# Optional video player libraries
try:
    import cv2                       # pip install opencv-python
    has_cv2 = True
except ImportError:
    has_cv2 = False

try:
    from tkvideoplayer import TkVideoPlayer  # pip install tkvideoplayer
    has_tkvideoplayer = True
except ImportError:
    has_tkvideoplayer = False
    
# Audio/Video playback options
try:
    import pyglet                    # pip install pyglet
    has_pyglet = True
except ImportError:
    has_pyglet = False

try:
    import pygame                    # pip install pygame
    import moviepy.editor as mp      # pip install moviepy
    pygame.mixer.init()
    has_pygame = True
    has_audio_support = True
except (ImportError, pygame.error):
    has_pygame = False
    has_audio_support = False
    
try:
    import vlc                       # pip install python-vlc
    has_vlc = True
except ImportError:
    has_vlc = False

# === DB selection utilities (Option 1) =====================================
from typing import List

STATE_FILE = Path.home() / ".mediavaultpro.json"

def scan_dbs(dir_path: str) -> List[str]:
    """List *.db files in a directory (non-recursive)."""
    p = Path(dir_path)
    return sorted([str(x) for x in p.glob("*.db") if x.is_file()])

def classify_db(db_path: str) -> str:
    """Return 'music' | 'visuals' | 'unknown' based on schema fingerprint."""
    try:
        con = sqlite3.connect(db_path)
        cur = con.cursor()
        cur.execute("SELECT name FROM sqlite_master WHERE type='table'")
        tables = {r[0].lower() for r in cur.fetchall()}
        music_hint   = {"tracks", "music_tracks", "albums", "artists"}
        visuals_hint = {"photos", "videos", "visuals", "media_items"}
        if tables & music_hint: return "music"
        if tables & visuals_hint: return "visuals"
        # column heuristics
        def cols(t):
            try:
                cur.execute(f"PRAGMA table_info('{t}')")
                return {c[1].lower() for c in cur.fetchall()}
            except sqlite3.DatabaseError:
                return set()
        for t in tables:
            c = cols(t)
            if {"rating_key","title","artist","album"}.issubset(c) or \
               {"rating_key","duration","genres"}.issubset(c):
                return "music"
        for t in tables:
            c = cols(t)
            if {"file_name","media_type","date_original"}.issubset(c) or \
               {"file_path","media_type","people"}.issubset(c):
                return "visuals"
        return "unknown"
    except Exception:
        return "unknown"
    finally:
        try: con.close()
        except Exception: pass

def load_state() -> dict:
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text())
        except Exception:
            return {}
    return {}

def save_state(**kwargs):
    st = load_state()
    st.update(kwargs)
    STATE_FILE.write_text(json.dumps(st, indent=2))
# ==========================================================================

# ---------------------------------------------------------------------------
# Globals & constants
# ---------------------------------------------------------------------------

DB_FILE = "Dereski_media_metadata_master.db"
PHOTOS_DIR = Path("photos_export")          # static path
JSONL_CHUNK = 4 * 1024 * 1024               # 4 MB

IMAGE_MAX = (500, 350)                      # preview size (w, h)
VIDEO_MAX = (500, 350)                      # video player size (w, h)

# Media file extensions
VIDEO_EXTENSIONS = {'.mp4', '.avi', '.mov', '.mkv', '.wmv', '.flv', '.webm', '.m4v', '.3gp'}
PHOTO_EXTENSIONS = {'.jpg', '.jpeg', '.png', '.gif', '.bmp', '.tiff', '.webp', '.heic'}
MUSIC_EXTENSIONS = {'.mp3', '.wav', '.flac', '.aac', '.ogg', '.m4a', '.wma'}

# ---------------------------------------------------------------------------
# Database helper
# ---------------------------------------------------------------------------

class MetadataDB:
    """Context‑manager wrapper around sqlite3 with JSON helper methods."""

    def __init__(self, db_path: str = DB_FILE):
        self.conn = sqlite3.connect(db_path)
        self.conn.row_factory = sqlite3.Row
        self._init_schema()
        self._migrate_database()

    # -- context management -------------------------------------------------
    def __enter__(self) -> "MetadataDB":
        return self

    def __exit__(self, exc_type, exc, tb):
        if exc:
            self.conn.rollback()
        else:
            self.conn.commit()
        self.conn.close()

    # -- schema -------------------------------------------------------------
    def _init_schema(self) -> None:
        cur = self.conn.cursor()
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS media (
                id            TEXT PRIMARY KEY,
                file_name     TEXT NOT NULL UNIQUE,
                media_type    TEXT,
                date_original TEXT,
                keywords      TEXT,
                genre         TEXT,
                duration      TEXT,
                file_path     TEXT,
                file_size     INTEGER,
                file_ext      TEXT,
                width         INTEGER,
                height        INTEGER,
                tags          TEXT,
                people        TEXT,
                location_name TEXT,
                location      TEXT,
                latitude      REAL,
                longitude     REAL,
                labels        TEXT,
                description   TEXT,
                date_added    TEXT,
                last_updated  TEXT,
                rating_key    TEXT
            )
            """
        )
        self.conn.commit()

    def _migrate_database(self) -> None:
        """Add missing columns to existing databases."""
        cur = self.conn.cursor()
        
        # Check existing columns
        cur.execute("PRAGMA table_info(media)")
        columns = [row[1] for row in cur.fetchall()]
        
        # List of new music-specific fields to add
        new_fields = {
            'rating_key': 'TEXT',
            'artist': 'TEXT',
            'album': 'TEXT', 
            'moods': 'TEXT',
            'year': 'TEXT',
            'album_summary': 'TEXT',
            'artist_summary': 'TEXT',
            'summary': 'TEXT',
            'bitrate': 'TEXT',
            'codec': 'TEXT',
            'channels': 'TEXT',
            'container': 'TEXT'
        }
        
        # Add missing columns
        for field_name, field_type in new_fields.items():
            if field_name not in columns:
                print(f"Adding {field_name} column to existing database...")
                cur.execute(f"ALTER TABLE media ADD COLUMN {field_name} {field_type}")
                
        self.conn.commit()
        print("Database migration completed.")

    # -- helpers ------------------------------------------------------------
    @staticmethod
    def _json_dump(obj: Any) -> str:
        return json.dumps(obj, separators=(",", ":"))

    @staticmethod
    def _json_load(text: Any) -> Any:
        if isinstance(text, (list, dict)) or text in (None, "", "None"):
            return text
        try:
            return json.loads(text)
        except (json.JSONDecodeError, TypeError):
            return text

    # -- import / merge -----------------------------------------------------
    def import_master(self, path: Path) -> int:
        """Load master data file (line‑delimited JSON). Returns # inserted."""
        cur = self.conn.cursor()
        inserted = 0
        with open(path, "r", encoding="utf‑8") as f:
            for line in f:
                if not line.strip():
                    continue
                data = json.loads(line)
                # normalise field names (master sample uses "File Name", etc.)
                record = {
                    "id": data.get("id") or os.urandom(8).hex(),
                    "file_name": data.get("File Name") or data.get("file_name"),
                    "media_type": data.get("Media Type"),
                    "date_original": data.get("Date Original"),
                    "keywords": self._json_dump(
                        MetadataDB._json_load(data.get("Keywords"))
                    ),
                    "genre": data.get("Genre"),
                    "duration": data.get("Duration"),
                    "file_path": data.get("File Path"),
                    "file_size": data.get("File Size"),
                    "file_ext": data.get("File Ext"),
                    "width": data.get("Width"),
                    "height": data.get("Height"),
                    "tags": self._json_dump(MetadataDB._json_load(data.get("Tags"))),
                    "people": self._json_dump(MetadataDB._json_load(data.get("People"))),
                    "location_name": self._json_dump(
                        MetadataDB._json_load(data.get("Location Name"))
                    ),
                    "location": self._json_dump(
                        MetadataDB._json_load(data.get("Location"))
                    ),
                    "latitude": data.get("Latitude"),
                    "longitude": data.get("Longitude"),
                    "labels": self._json_dump(MetadataDB._json_load(data.get("Labels"))),
                    "description": data.get("Description"),
                    "date_added": data.get("Date Added"),
                    "last_updated": data.get("Last Updated"),
                    "rating_key": data.get("Rating Key") or data.get("rating_key"),
                }
                try:
                    cur.execute(
                        """
                        INSERT OR IGNORE INTO media(
                            id,file_name,media_type,date_original,keywords,genre,duration,
                            file_path,file_size,file_ext,width,height,tags,people,
                            location_name,location,latitude,longitude,labels,description,
                            date_added,last_updated,rating_key
                        ) VALUES(
                            :id,:file_name,:media_type,:date_original,:keywords,:genre,:duration,
                            :file_path,:file_size,:file_ext,:width,:height,:tags,:people,
                            :location_name,:location,:latitude,:longitude,:labels,:description,
                            :date_added,:last_updated,:rating_key
                        )
                        """,
                        record,
                    )
                    inserted += cur.rowcount
                except sqlite3.IntegrityError as err:
                    print("DB error:", err, file=sys.stderr)
        self.conn.commit()
        return inserted

    def merge_updates(self, path: Path) -> int:
        """Apply AI‑enriched updates. Returns # rows updated."""
        cur = self.conn.cursor()
        updated = 0
        with open(path, "r", encoding="utf‑8") as f:
            for line in f:
                if not line.strip():
                    continue
                data = json.loads(line)
                cur.execute(
                    """
                    UPDATE media
                       SET keywords      = :keywords,
                           location_name = :location_name,
                           description   = :description,
                           last_updated  = datetime('now')
                     WHERE id = :id OR file_name = :file_name
                    """,
                    {
                        "keywords": self._json_dump(data.get("keywords")),
                        "location_name": self._json_dump(data.get("location_name")),
                        "description": data.get("description"),
                        "id": data.get("id"),
                        "file_name": data.get("file_name"),
                    },
                )
                updated += cur.rowcount
        self.conn.commit()
        return updated

    def fix_file_paths(self, base_path: str, file_names: List[str]) -> int:
        """Update file_path entries for specific files to point to a custom base directory."""
        cur = self.conn.cursor()
        
        updated = 0
        base_path_obj = Path(base_path)
        
        for file_name in file_names:
            if not file_name or file_name.strip() == "":
                continue
                
            # Create the full path: base_path + filename
            new_path = str(base_path_obj / file_name)
            
            cur.execute(
                "UPDATE media SET file_path = ?, last_updated = datetime('now') WHERE file_name = ?",
                (new_path, file_name)
            )
            updated += cur.rowcount
            
        self.conn.commit()
        return updated

    # -- query --------------------------------------------------------------
    def search(self, query: str) -> List[sqlite3.Row]:
        """Search for media records across all relevant text fields."""
        cur = self.conn.cursor()
        q = f"%{query.lower()}%"
        cur.execute(
            """
            SELECT *
              FROM media
             WHERE lower(file_name)     LIKE ?
                OR lower(id)            LIKE ?
                OR lower(description)   LIKE ?
                OR lower(location_name) LIKE ?
                OR lower(keywords)      LIKE ?
                OR lower(people)        LIKE ?
                OR lower(labels)        LIKE ?
                OR lower(tags)          LIKE ?
             ORDER BY file_name
            """,
            (q, q, q, q, q, q, q, q),
        )
        return cur.fetchall()

    def search_filtered(self, query: str = "", filter_type: str = "All") -> List[sqlite3.Row]:
        """Search for media records with optional media type filtering."""
        cur = self.conn.cursor()
        
        # Base query
        base_query = """
            SELECT *
              FROM media
             WHERE 1=1
        """
        params = []
        
        # Add search filter if query provided
        if query.strip():
            q = f"%{query.lower()}%"
            base_query += """
                AND (lower(file_name)     LIKE ?
                  OR lower(id)            LIKE ?
                  OR lower(description)   LIKE ?
                  OR lower(location_name) LIKE ?
                  OR lower(keywords)      LIKE ?
                  OR lower(people)        LIKE ?
                  OR lower(labels)        LIKE ?
                  OR lower(tags)          LIKE ?)
            """
            params.extend([q, q, q, q, q, q, q, q])
        
        # Add media type filter
        if filter_type == "Photos":
            # Photos stored with dots in database
            photo_exts = "', '".join(ext for ext in PHOTO_EXTENSIONS)
            base_query += f" AND lower(file_ext) IN ('{photo_exts}')"
            base_query += " ORDER BY file_name"
        elif filter_type == "Videos":
            # Videos stored with dots in database  
            video_exts = "', '".join(ext for ext in VIDEO_EXTENSIONS)
            base_query += f" AND lower(file_ext) IN ('{video_exts}')"
            base_query += " ORDER BY file_name"
        elif filter_type == "Music":
            # Music stored without dots in database
            music_exts = "', '".join(ext.lstrip('.') for ext in MUSIC_EXTENSIONS)
            base_query += f" AND lower(file_ext) IN ('{music_exts}')"
            base_query += " ORDER BY file_name"
        elif filter_type == "Music: Album":
            # Music files grouped by album
            music_exts = "', '".join(ext.lstrip('.') for ext in MUSIC_EXTENSIONS)
            base_query += f" AND lower(file_ext) IN ('{music_exts}') AND album IS NOT NULL AND album != '' AND album != 'None'"
            base_query += " ORDER BY album, track_number, file_name"
        elif filter_type == "Music: Artist":
            # Music files grouped by artist  
            music_exts = "', '".join(ext.lstrip('.') for ext in MUSIC_EXTENSIONS)
            base_query += f" AND lower(file_ext) IN ('{music_exts}') AND artist IS NOT NULL AND artist != '' AND artist != 'None'"
            base_query += " ORDER BY artist, album, track_number, file_name"
        elif filter_type == "Music: Genre":
            # Music files grouped by genre
            music_exts = "', '".join(ext.lstrip('.') for ext in MUSIC_EXTENSIONS)
            base_query += f" AND lower(file_ext) IN ('{music_exts}') AND genre IS NOT NULL AND genre != '' AND genre != 'None'"
            base_query += " ORDER BY genre, artist, album, track_number, file_name"
        elif filter_type == "Music: Mood":
            # Music files filtered by mood
            music_exts = "', '".join(ext.lstrip('.') for ext in MUSIC_EXTENSIONS)
            base_query += f" AND lower(file_ext) IN ('{music_exts}') AND moods IS NOT NULL AND moods != '' AND moods != '[]'"
            base_query += " ORDER BY moods, artist, file_name"
        elif filter_type == "Music: Year":
            # Music files grouped by year
            music_exts = "', '".join(ext.lstrip('.') for ext in MUSIC_EXTENSIONS)
            base_query += f" AND lower(file_ext) IN ('{music_exts}') AND year IS NOT NULL AND year != ''"
            base_query += " ORDER BY year DESC, artist, album, track_number"
        else:
            # "All" and other cases - default sort
            base_query += " ORDER BY file_name"
        
        cur.execute(base_query, params)
        return cur.fetchall()

    def add_new_media(self, file_path: Path) -> str | None:
        """Add a new media file to the database."""
        if not file_path.exists():
            return None

        # Copy file to the photos_export directory
        PHOTOS_DIR.mkdir(exist_ok=True)
        dest_path = PHOTOS_DIR / file_path.name
        shutil.copy2(file_path, dest_path)

        cur = self.conn.cursor()
        new_id = os.urandom(8).hex()
        file_name = dest_path.name
        
        record = {
            "id": new_id,
            "file_name": file_name,
            "file_path": str(dest_path),
            "media_type": "image" if file_path.suffix.lower() not in VIDEO_EXTENSIONS else "video",
            "date_added": datetime.now().isoformat(),
            "last_updated": datetime.now().isoformat(),
        }

        try:
            cur.execute(
                """
                INSERT INTO media (id, file_name, file_path, media_type, date_added, last_updated)
                VALUES (:id, :file_name, :file_path, :media_type, :date_added, :last_updated)
                """,
                record,
            )
            self.conn.commit()
            return file_name
        except sqlite3.IntegrityError as err:
            print(f"Error adding new media: {err}", file=sys.stderr)
            return None

    def fetch_all(self) -> List[sqlite3.Row]:
        cur = self.conn.cursor()
        cur.execute("SELECT * FROM media ORDER BY file_name")
        return cur.fetchall()

    def fetch_one(self, file_name: str) -> sqlite3.Row | None:
        cur = self.conn.cursor()
        cur.execute("SELECT * FROM media WHERE file_name = ?", (file_name,))
        return cur.fetchone()

    def save_record(
        self,
        file_name: str,
        keywords: List[str],
        location_name: str | Dict[str, Any],
        description: str,
        people: List[str],
        labels: List[str],
    ) -> None:
        cur = self.conn.cursor()
        cur.execute(
            """
            UPDATE media
               SET keywords      = ?,
                   location_name = ?,
                   description   = ?,
                   people        = ?,
                   labels        = ?,
                   last_updated  = datetime('now')
             WHERE file_name = ?
            """,
            (
                self._json_dump(keywords),
                self._json_dump(location_name),
                description,
                self._json_dump(people),
                self._json_dump(labels),
                file_name,
            ),
        )
        self.conn.commit()

    # ------------------------------------------------------------------
    # EXPORT for OpenAI vector‑store
    # ------------------------------------------------------------------

    def export_jsonl(
        self,
        out_dir: Path,
        chunk_size: int = JSONL_CHUNK,
        *,
        include_all_fields: bool = True,
        fields: Tuple[str, ...] = None,
        ) -> int:
        """
        Export database records to JSONL chunks.
        
        • Set include_all_fields=True to export all DB columns (default)
        • Or specify particular fields to export
        • Chunk files (=<chunk_size bytes) land in `out_dir`  
        • Returns the number of chunk files written
        """
        # Make sure out_dir is a Path object
        if isinstance(out_dir, str):
            out_dir = Path(out_dir)
        
        # Create the directory if it doesn't exist
        out_dir.mkdir(parents=True, exist_ok=True)
    
        cur = self.conn.cursor()
    
        # Get all column names if we need all fields
        if include_all_fields or fields is None:
            cur.execute("PRAGMA table_info(media)")
            fields = tuple(row[1] for row in cur.fetchall())
    
        # Make sure we're selecting valid fields
        fields_str = ", ".join(f'"{field}"' for field in fields)
        cur.execute(f"SELECT {fields_str} FROM media")
    
        chunk_idx, current_size = 0, 0
        outfile_path = out_dir / f"media_chunk_{chunk_idx:04d}.jsonl"
        print(f"Creating export file: {outfile_path}")  # Debug print
    
        outfile = outfile_path.open("w", encoding="utf-8")

        def process_row(row: sqlite3.Row) -> dict:
            """Convert row to a dictionary with processed values."""
            result = {}
            for col in fields:
                val = row[col]
                # Decode JSON columns back to Python objects
                if col in {
                    "id",
                    "file_name",
                    "media_type",
                    "date_original",
                    "keywords",
                    "genre",
                    "duration",
                    "file_path",
                    "file_size",
                    "file_ext",
                    "width",
                    "height",
                    "tags",
                    "people",
                    "location_name",
                    "location",
                    "latitude",
                    "longitude",
                    "labels",
                    "description",
                    "date_added",
                    "last_updated",
                    "rating_key",
                    }:
                    try:
                        val = self._json_load(val)
                    except Exception as e:
                        print(f"Warning: Could not parse JSON for {col}: {e}")
                    result[col] = val
            return result

        records_processed = 0
        for row in cur:
            # Convert the row to JSON
            try:
                record = process_row(row)
                line = json.dumps(record, ensure_ascii=False, default=str) + "\n"
                
                # Split into chunks when necessary
                if current_size + len(line.encode("utf-8")) > chunk_size:
                    outfile.close()
                    chunk_idx += 1
                    outfile_path = out_dir / f"media_chunk_{chunk_idx:04d}.jsonl"
                    print(f"Creating export file: {outfile_path}")  # Debug print
                    outfile = outfile_path.open("w", encoding="utf-8")
                    current_size = 0

                outfile.write(line)
                current_size += len(line.encode("utf-8"))
                records_processed += 1
            
                # Print progress every 100 records
                if records_processed % 100 == 0:
                    print(f"Processed {records_processed} records...")
        
            except Exception as e:
                print(f"Error processing record: {e}")
                continue

        outfile.close()
        print(f"Export complete: {records_processed} records in {chunk_idx + 1} files")
        return chunk_idx + 1

# ---------------------------------------------------------------------------
# GUI
# ---------------------------------------------------------------------------

class QueueManager:
    """Manages smart queue detection and recreation for Apple Music integration."""
    
    def __init__(self):
        self.last_queue_time = None
        self.queue_timeout = 300  # 5 minutes
        self.local_queue = []  # [(file_path, song_name), ...]
        self.current_temp_playlist = None
    
    def has_active_queue(self):
        """Check if we have an active queue based on timing and music state."""
        if not self.last_queue_time:
            return False
        
        import time
        time_since = time.time() - self.last_queue_time
        return time_since < self.queue_timeout
    
    def get_current_playlist_songs_from_position(self):
        """Get remaining songs from current Music app playlist starting from current track."""
        try:
            import subprocess
            
            # Simpler approach: get all tracks from current playlist
            script = '''
            tell application "Music"
                try
                    set currentPlaylist to current playlist
                    set allTracks to tracks of currentPlaylist
                    set songsList to {}
                    
                    repeat with currentTrack in allTracks
                        try
                            set trackLocation to location of currentTrack
                            if trackLocation is not missing value then
                                set trackPath to POSIX path of trackLocation
                                set trackName to name of currentTrack
                                set end of songsList to trackPath & "|" & trackName
                            end if
                        on error
                            -- Skip tracks without location
                        end try
                    end repeat
                    
                    return songsList
                on error errMsg
                    return {"error:" & errMsg}
                end try
            end tell
            '''
            
            result = subprocess.run(['osascript', '-e', script],
                                 capture_output=True, text=True, timeout=15)
            
            if result.returncode == 0:
                output = result.stdout.strip()
                print(f"Raw AppleScript output: {output}")
                
                if not output or output == "{}":
                    return []
                
                # Handle AppleScript list format
                if output.startswith('{') and output.endswith('}'):
                    output = output[1:-1]  # Remove braces
                
                songs_data = [item.strip(' "') for item in output.split(', ') if item.strip()]
                songs = []
                for song_data in songs_data:
                    if '|' in song_data:
                        path, name = song_data.split('|', 1)
                        songs.append((path.strip(), name.strip()))
                        
                print(f"Parsed {len(songs)} songs from current playlist")
                return songs
            else:
                print(f"Error getting playlist songs: {result.stderr}")
                return []
                
        except Exception as e:
            print(f"Error reading current playlist: {e}")
            return []
    
    def smart_add_to_queue(self, file_path, song_name, music_app_handler):
        """Intelligently add song to queue, preserving existing queue when possible."""
        import time
        
        print(f"\n=== SMART QUEUE DEBUG ===")
        print(f"Adding song: {song_name}")
        print(f"File path: {file_path}")
        print(f"Has active queue: {self.has_active_queue()}")
        print(f"Last queue time: {self.last_queue_time}")
        print(f"Local queue length: {len(self.local_queue)}")
        
        if self.has_active_queue():
            # Try to read current playlist and preserve remaining songs
            print("Active queue detected, attempting to preserve existing songs")
            current_songs = self.get_current_playlist_songs_from_position()
            
            if current_songs:
                # Merge existing queue with new song
                new_queue = current_songs + [(file_path, song_name)]
                print(f"Preserving {len(current_songs)} existing songs, adding new song")
                for i, (path, name) in enumerate(current_songs):
                    print(f"  {i+1}. {name}")
                print(f"  {len(current_songs)+1}. {song_name} (NEW)")
            else:
                # Fallback to local queue + new song
                new_queue = self.local_queue + [(file_path, song_name)]
                print("Could not read current playlist, using local queue")
        else:
            # Start fresh queue
            new_queue = [(file_path, song_name)]
            print("Starting fresh queue")
        
        # Update local queue state
        self.local_queue = new_queue.copy()
        
        print(f"Final queue length: {len(new_queue)}")
        
        # Recreate playlist with new queue
        success = music_app_handler._recreate_playlist_with_queue(new_queue)
        
        if success:
            self.last_queue_time = time.time()
            print(f"✓ Queue updated with {len(new_queue)} songs")
        else:
            print("✗ Failed to update queue")
        
        print(f"=========================\n")
        return success
    
    def clear_queue_state(self):
        """Clear queue state - call when user manually changes music or app restarts."""
        self.last_queue_time = None
        self.local_queue = []
        self.current_temp_playlist = None


class MetadataEditorApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Media Metadata Editor")
        self.geometry("1200x750")
        self.minsize(1000, 650)
        
        # Add full-screen support attributes
        self.fullscreen_window = None
        self.is_fullscreen = False
        self.fullscreen_video_player = None
        self.fullscreen_canvas = None

        self.current_video_process = None  # manage video windows
        self.current_audio_process = None  # manage audio players
        
        # Initialize queue manager for smart music queue handling
        self.queue_manager = QueueManager()
        
        # Set theme colors
        self.bg_color = "#f0f4f8"
        self.accent_color = "#4a90e2"
        self.text_color = "#333333"
        
        self.configure(bg=self.bg_color)
        self.style = ttk.Style()
        self.style.theme_use('alt')  # Use alternate theme as base
        
        # Configure styles
        self.style.configure("TFrame", background=self.bg_color)
        self.style.configure("TLabel", background=self.bg_color, foreground=self.text_color)
        self.style.configure("TButton", background=self.accent_color, foreground="white")
        self.style.configure("Treeview", background="white", foreground=self.text_color, rowheight=25)
        self.style.configure("Treeview.Heading", font=('Helvetica', 10, 'bold'))
        
        # Set up copy-paste bindings
        self.setup_copy_paste()
        
        # Create menu
        self.create_menu()
        
        # Initialize database
        self.db = MetadataDB()
        
        # Set up proper window closing handler
        self.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # Load last-used DB if available
        try:
            st = load_state()
            last_db = st.get("current_db")
            if last_db and Path(last_db).exists() and st.get("current_media_kind") == "visuals":
                self.set_database(last_db)
        except Exception:
            pass

        self.current_file = None
        
        # Create default image for preview
        self.default_img = None
        
        # Current media properties
        self.current_img = None
        self.current_img_rotation = 0
        
        # Video player references
        self.video_player = None
        self.video_frame = None
        self.current_video_path = None
        self.video_playing = False
        self.video_rotation = 0
        
        # Audio player references
        self.vlc_instance = None
        self.vlc_player = None
        self.vlc_media = None
        self.pygame_player = None
        
        # Initialize VLC if available
        if has_vlc:
            try:
                self.vlc_instance = vlc.Instance('--no-xlib')
            except Exception as e:
                print(f"VLC initialization error: {e}")
                self.vlc_instance = None
        
        # Build UI
        self._build_widgets()
        self._populate_tree()
        
    def setup_copy_paste(self):
        """Set up copy-paste bindings for entry and text widgets."""
        # Define key bindings for copy, cut, paste
        self.copy_paste_bindings = {
            # Windows/Linux bindings
            '<Control-c>': self.copy_text,
            '<Control-x>': self.cut_text,
            '<Control-v>': self.paste_text,
            # Mac bindings
            '<Command-c>': self.copy_text,
            '<Command-x>': self.cut_text,
            '<Command-v>': self.paste_text,
        }

    # ────────────────────────────────────────────────────────────────────────
    #  CLIPBOARD + MOUSE COPY/PASTE  (replace the old helper)
    # ────────────────────────────────────────────────────────────────────────
    def apply_copy_paste_bindings(self, widget: tk.Widget) -> None:
        """
        Attach keyboard shortcuts **and** a right-click / middle-click context
        menu that offers Cut / Copy / Paste.  Also routes all paste actions
        through self.paste_text so text is inserted only once.
        """

        # Avoid binding the same widget more than once
        if getattr(widget, "_context_menu_installed", False):
            return
        widget._context_menu_installed = True

        # -------- context (right-click) menu ----------
        menu = tk.Menu(widget, tearoff=0)
        menu.add_command(label="Cut",   command=lambda w=widget: w.event_generate("<<Cut>>"))
        menu.add_command(label="Copy",  command=lambda w=widget: w.event_generate("<<Copy>>"))
        menu.add_command(label="Paste", command=lambda w=widget: w.event_generate("<<Paste>>"))

        # Button-3 = right click on most systems (mac trackpads map it too)
        widget.bind("<Button-3>", lambda e, m=menu: m.tk_popup(e.x_root, e.y_root), add="+")
        # Button-2 = middle click (classic X-11 quick-paste)
        widget.bind("<Button-2>", lambda e: widget.event_generate("<<Paste>>"),      add="+")

        # -------- keyboard shortcuts ----------
        widget.bind("<Control-c>", lambda e: widget.event_generate("<<Copy>>"),  add="+")
        widget.bind("<Control-x>", lambda e: widget.event_generate("<<Cut>>"),   add="+")
        widget.bind("<Control-v>", lambda e: widget.event_generate("<<Paste>>"), add="+")

        # Route ALL paste events through your existing handler – it already
        # returns "break", preventing the default Tk paste (so no duplicates).
        widget.bind("<<Paste>>", self.paste_text, add="+")
        
    def copy_text(self, event):
        """Copy selected text to clipboard."""
        try:
            widget = event.widget
            if isinstance(widget, tk.Entry) or isinstance(widget, ttk.Entry):
                if widget.selection_present():
                    selected_text = widget.selection_get()
                    self.clipboard_clear()
                    self.clipboard_append(selected_text)
            elif isinstance(widget, tk.Text):
                if widget.tag_ranges("sel"):
                    selected_text = widget.get("sel.first", "sel.last")
                    self.clipboard_clear()
                    self.clipboard_append(selected_text)
        except Exception as e:
            print(f"Copy error: {e}")
    
    def cut_text(self, event):
        """Cut selected text to clipboard."""
        try:
            widget = event.widget
            if isinstance(widget, tk.Entry) or isinstance(widget, ttk.Entry):
                if widget.selection_present():
                    selected_text = widget.selection_get()
                    self.clipboard_clear()
                    self.clipboard_append(selected_text)
                    widget.delete("sel.first", "sel.last")
            elif isinstance(widget, tk.Text):
                if widget.tag_ranges("sel"):
                    selected_text = widget.get("sel.first", "sel.last")
                    self.clipboard_clear()
                    self.clipboard_append(selected_text)
                    widget.delete("sel.first", "sel.last")
        except Exception as e:
            print(f"Cut error: {e}")
    
    def paste_text(self, event):
        """Paste clipboard text into widget."""
        try:
            widget = event.widget
            text_to_paste = self.clipboard_get()
            
            if isinstance(widget, tk.Entry) or isinstance(widget, ttk.Entry):
                if widget.selection_present():
                    widget.delete("sel.first", "sel.last")
                widget.insert("insert", text_to_paste)
            elif isinstance(widget, tk.Text):
                if widget.tag_ranges("sel"):
                    widget.delete("sel.first", "sel.last")
                widget.insert("insert", text_to_paste)
            return "break"
        except Exception as e:
            print(f"Paste error: {e}")
            return "break"

    # ────────────────────────────────────────────────────────────────────────
    #  CONTEXT-MENU / MOUSE PASTE  (new)
    # ────────────────────────────────────────────────────────────────────────
    def _attach_context_menu(self, widget: tk.Widget):
        """Add right-click menu + middle-click paste to a widget."""
        menu = tk.Menu(widget, tearoff=0)
        menu.add_command(label="Cut",
                         command=lambda w=widget: w.event_generate("<<Cut>>"))
        menu.add_command(label="Copy",
                         command=lambda w=widget: w.event_generate("<<Copy>>"))
        menu.add_command(label="Paste",
                         command=lambda w=widget: w.event_generate("<<Paste>>"))

        # right-click (Windows / macOS) = <Button-2> on mac trackpads, <Button-3> elsewhere
        widget.bind("<Button-3>", lambda e, m=menu: m.tk_popup(e.x_root, e.y_root))
        # middle-click paste (common on Linux / X11)
        widget.bind("<Button-2>", lambda e: widget.event_generate("<<Paste>>"))
        # make sure our custom paste suppresses double-insert
        widget.bind("<<Paste>>", self.paste_text, add="+")
        
    def create_menu(self):
        menubar = tk.Menu(self)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Add New Media", command=self.on_add_media)
        file_menu.add_separator()
        file_menu.add_command(label="Import Master Data", command=self.on_import_master)
        file_menu.add_command(label="Merge Updates", command=self.on_merge_updates)
        file_menu.add_separator()
        file_menu.add_command(label="Export to JSONL", command=self.on_export_jsonl)
        file_menu.add_separator()
        file_menu.add_command(label="Update Music Data...", command=self.on_update_music_data)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        # Database menu (Option 1: dropdown dialog)
        db_menu = tk.Menu(menubar, tearoff=0)
        db_menu.add_command(label="Select Database…", command=self.on_select_database)
        db_menu.add_separator()
        db_menu.add_command(label="Fix File Paths", command=self.on_fix_file_paths)
        menubar.add_cascade(label="Database", menu=db_menu)
        
        # Edit menu
        edit_menu = tk.Menu(menubar, tearoff=0)
        edit_menu.add_command(label="Search", command=lambda: self.search_entry.focus())
        menubar.add_cascade(label="Edit", menu=edit_menu)
        
        # Image menu
        image_menu = tk.Menu(menubar, tearoff=0)
        image_menu.add_command(label="Rotate Left", command=lambda: self.rotate_image(-90))
        image_menu.add_command(label="Rotate Right", command=lambda: self.rotate_image(90))
        image_menu.add_command(label="Save Rotation", command=self.save_rotated_image)
        menubar.add_cascade(label="Image", menu=image_menu)

        # Video menu
        video_menu = tk.Menu(menubar, tearoff=0)
        video_menu.add_command(label="Rotate Left", command=lambda: self.rotate_video(-90))
        video_menu.add_command(label="Rotate Right", command=lambda: self.rotate_video(90))
        video_menu.add_separator()
        video_menu.add_command(label="Save Rotation", command=self.save_rotated_video)
        menubar.add_cascade(label="Video", menu=video_menu)
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="About", command=lambda: messagebox.showinfo(
            "About", "Media Metadata Editor\nVersion 1.0\n\nFor editing and managing media metadata"
        ))
        menubar.add_cascade(label="Help", menu=help_menu)
        
        self.config(menu=menubar)

    def on_add_media(self):
        """Callback to add a new media file."""
        file_paths = filedialog.askopenfilenames(
            title="Select Media Files to Add",
            filetypes=[("Media Files", "*.jpg *.jpeg *.png *.gif *.mp4 *.avi *.mov *.mkv"), ("All files", "*.*")]
        )
        if not file_paths:
            return

        added_count = 0
        for file_path_str in file_paths:
            file_path = Path(file_path_str)
            new_file_name = self.db.add_new_media(file_path)
            if new_file_name:
                added_count += 1
        
        if added_count > 0:
            self._populate_tree()
            messagebox.showinfo("Success", f"Added {added_count} new media file(s).")
    
    def save_rotated_image(self):
        """Save the rotated image to disk, preserving metadata if possible."""
        if not self.current_img or not hasattr(self, 'current_img_path') or not self.current_img_path:
            messagebox.showerror("Error", "No image to save")
            return
            
        if self.current_img_rotation == 0:
            messagebox.showinfo("Info", "No rotation to save")
            return
            
        try:
            # Create a backup of the original file
            backup_path = str(self.current_img_path) + ".backup"
            if not os.path.exists(backup_path):
                import shutil
                shutil.copy2(self.current_img_path, backup_path)
                
            # Extract metadata if possible (EXIF, etc.)
            metadata = None
            try:
                # For JPEG images, try to extract EXIF data
                if self.current_img_path.suffix.lower() in {".jpg", ".jpeg"}:
                    exif = self.current_img.info.get('exif')
                    metadata = {'exif': exif} if exif else None
                    
                # For other metadata types (e.g., PNG metadata, etc.)
                for key, value in self.current_img.info.items():
                    if key not in {'exif'}:  # Already handled exif
                        if metadata is None:
                            metadata = {}
                        metadata[key] = value
            except Exception as e:
                print(f"Error extracting metadata: {e}")
                
            # Apply rotation and save (negative angle for clockwise rotation to match preview)
            rotated_img = self.current_img.rotate(-self.current_img_rotation, expand=True)
            
            # Save the rotated image, preserving metadata if available
            if metadata:
                rotated_img.save(self.current_img_path, **metadata)
            else:
                rotated_img.save(self.current_img_path)
            
            # Close the image to ensure file handles are released
            rotated_img.close()
            if hasattr(self, 'current_img') and self.current_img:
                self.current_img.close()
                
            # Reload the image from disk to ensure we're displaying the saved version
            self.current_img_rotation = 0  # Reset rotation angle after saving
            
            try:
                # Wait a moment for the file to be fully written
                self.after(100)
                # Reload the image from disk
                self.current_img = Image.open(self.current_img_path)
                self.display_image()
                
                messagebox.showinfo("Success", 
                                   f"Image saved with rotation applied.\nBackup created at {backup_path}")
            except Exception as e:
                print(f"Error reloading image after save: {e}")
                messagebox.showwarning("Warning", 
                                      f"Image was saved, but there was an error reloading it: {e}")
                # Force reload of current record
                self.load_record(self.current_file)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save rotated image: {e}")
            print(f"Error saving rotated image: {e}")
            # Attempt to reload the original file
            try:
                self.load_record(self.current_file)
            except Exception:
                pass

    # ────────────────────────────────────────────────────────────────────────
    #  VIDEO ROTATION - Corrected
    # ────────────────────────────────────────────────────────────────────────

    def rotate_video(self, angle: int) -> None:
        """Queue a 90/180/270° rotation for the current video preview."""
        if not (self.current_file and self.current_file.lower().endswith(tuple(VIDEO_EXTENSIONS))):
            return  # not a video → ignore

        # keep rotation in 0-359 range
        self.video_rotation = (self.video_rotation + angle) % 360
        # Refresh the video preview to show the intended rotation
        if self.video_playing:
            self.play_video_cv2() # Re-render with new rotation
        else:
             # Just show a rotated thumbnail if possible
            if has_cv2 and self.current_video_path:
                self.display_video_thumbnail(self.current_video_path)

    def save_rotated_video(self) -> None:
        """Rotate video file using ffmpeg and replace the original."""
        if self.video_rotation == 0:
            messagebox.showinfo("Rotate", "No rotation to save.")
            return
        if shutil.which("ffmpeg") is None:
            messagebox.showerror("Rotate", "FFmpeg not found on your system's PATH. Please install it to rotate videos.")
            return

        src = self.current_video_path
        if not src or not src.exists():
            messagebox.showerror("Rotate", f"Source file not found: {src}")
            return

        transpose_map = {90: "transpose=1", 180: "transpose=1,transpose=1", 270: "transpose=2"}
        rotate_filter = transpose_map.get(self.video_rotation)
        if not rotate_filter:
            messagebox.showerror("Rotate", f"Unsupported rotation angle: {self.video_rotation}°")
            return

        # Create a temporary file for the output
        with tempfile.NamedTemporaryFile(dir=src.parent, suffix=src.suffix, delete=False) as tmp:
            tmp_path = Path(tmp.name)

        cmd = [
            "ffmpeg", "-y",
            "-i", str(src),
            "-vf", rotate_filter,
            "-c:v", "libx264", "-preset", "medium", "-crf", "23", # Good balance of quality and size
            "-c:a", "copy",  # Copy audio stream without re-encoding
            str(tmp_path),
        ]

        # --- Progress Dialog ---
        progress_window = tk.Toplevel(self)
        progress_window.title("Rotating Video")
        progress_window.geometry("350x120")
        progress_window.transient(self)
        progress_window.grab_set()
        progress_window.resizable(False, False)
        
        label = tk.Label(progress_window, text="Processing video, please wait...")
        label.pack(pady=10)
        progress = ttk.Progressbar(progress_window, mode="indeterminate", length=300)
        progress.pack(pady=10)
        progress.start(10)

        def run_ffmpeg_thread():
            try:
                # Using PIPE for stderr to capture potential errors
                process = subprocess.Popen(cmd, stderr=subprocess.PIPE, universal_newlines=True)
                _, stderr = process.communicate() # Wait for completion

                if process.returncode == 0:
                    # Success: replace original file
                    shutil.move(str(tmp_path), src)
                    self.video_rotation = 0  # Reset rotation
                    
                    self.after(0, progress_window.destroy)
                    self.after(0, lambda: messagebox.showinfo("Success", "Video rotated and saved successfully."))
                    # Reload the video in the player
                    self.after(10, lambda: self.load_record(self.current_file))
                else:
                    # Failure
                    if tmp_path.exists():
                        tmp_path.unlink()
                    self.after(0, progress_window.destroy)
                    self.after(0, lambda: messagebox.showerror("FFmpeg Error", f"Failed to rotate video.\n\nError:\n{stderr[-500:]}"))
            
            except Exception as e:
                if tmp_path.exists():
                    tmp_path.unlink()
                self.after(0, progress_window.destroy)
                self.after(0, lambda: messagebox.showerror("Error", f"An unexpected error occurred: {e}"))

        # Run ffmpeg in a separate thread to avoid freezing the GUI
        threading.Thread(target=run_ffmpeg_thread, daemon=True).start()
    
    def reload_current_video(self):
        """Reload the current video after processing."""
        # Save the current position if playing
        was_playing = False
        position = 0
        if hasattr(self, 'video_player') and self.video_player:
            try:
                was_playing = self.video_player.is_playing()
                position = self.video_player.get_position()
            except:
                pass
        
        # Close existing video
        if hasattr(self, 'close_video'):
            self.close_video()
        
        # Reload the same file
        if hasattr(self, 'load_video'):
            self.load_video(self.current_file)
            
            # Restore playback state
            if was_playing and position > 0:
                # Wait a bit to ensure video is loaded
                self.after(500, lambda: self.seek_and_play(position))

    def seek_and_play(self, position):
        """Helper to seek to position and play if needed."""
        if hasattr(self, 'video_player') and self.video_player:
            try:
                self.video_player.set_position(position)
                self.video_player.play()
            except:
                pass

    # ---------------------------------------------------------------------
    #  GUI construction
    # ---------------------------------------------------------------------
    def _build_widgets(self) -> None:
        """Create the main split‑pane UI: file list on the left, editor on the right."""
        # ----- outer paned window ----------------------------------------
        pane = ttk.PanedWindow(self, orient="horizontal")
        pane.pack(fill="both", expand=True, padx=10, pady=10)

        # ========== LEFT  – file list =====================================
        left_frame = ttk.Frame(pane)
        pane.add(left_frame, weight=1)           # let the list stretch
        
        # Filter controls
        filter_frame = ttk.Frame(left_frame, padding=(0, 0, 0, 8))
        filter_frame.pack(fill="x")
        
        ttk.Label(filter_frame, text="Filter:").pack(side="left")
        self.filter_var = tk.StringVar(value="All")
        self.filter_combo = ttk.Combobox(filter_frame, textvariable=self.filter_var, 
                                        values=["All", "Photos", "Videos", "Music", "Music: Album", "Music: Artist", "Music: Genre", "Music: Mood", "Music: Year"], 
                                        state="readonly", width=15)
        self.filter_combo.pack(side="left", padx=(5, 0))
        self.filter_combo.bind("<<ComboboxSelected>>", self.on_filter_change)
        
        # Back button for drill-down navigation (initially hidden)
        self.back_button = ttk.Button(filter_frame, text="← Back", command=self.on_back_button)
        self.back_button.pack(side="left", padx=(10, 0))
        self.back_button.pack_forget()  # Hide initially
        
        # Play All button for music playback (initially hidden)
        self.play_all_button = ttk.Button(filter_frame, text="🎵 Play All", command=self.on_play_all)
        self.play_all_button.pack(side="left", padx=(5, 0))
        self.play_all_button.pack_forget()  # Hide initially
        
        # Navigation state tracking
        self.navigation_state = {
            "is_drilled_down": False,
            "parent_filter": None,
            "selected_category": None,
            "category_songs": None
        }
        
        # Search bar
        search_frame = ttk.Frame(left_frame, padding=(0, 0, 0, 8))
        search_frame.pack(fill="x")
        
        ttk.Label(search_frame, text="Search:").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(search_frame, textvariable=self.search_var)
        self.search_entry.pack(side="left", fill="x", expand=True, padx=(5, 0))
        self.search_entry.bind("<Return>", self.on_search)
        self.apply_copy_paste_bindings(self.search_entry)
        
        # Add live search - search as user types with small delay
        self.search_timer = None
        self.search_var.trace('w', self.on_search_change)
        
        ttk.Button(search_frame, text="Search", command=lambda: self.on_search(None)).pack(side="right", padx=(5, 0))

        # File list
        tree_frame = ttk.Frame(left_frame)
        tree_frame.pack(fill="both", expand=True)
        
        self.tree = ttk.Treeview(
            tree_frame,
            columns=("description", "desc"),
            show="headings",
            selectmode="browse",
            height=25,
        )
        self.tree.heading("description", text="File Name")
        self.tree.heading("desc", text="Description")
        self.tree.column("description", width=250)
        self.tree.column("desc", width=80)
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree.bind("<Double-1>", self.on_tree_double_click)

        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")

        # ========== RIGHT – metadata editor ===============================
        right_frame = ttk.Frame(pane, padding=16)
        pane.add(right_frame, weight=2)          # give enough space for the editor
        
        # –– Preview frame (for both image and video) ––––––––––––––––––––––––
        self.preview_frame = ttk.Frame(right_frame, padding=(0, 0, 0, 10))
        self.preview_frame.pack(fill="x")
        
        # Default preview label for images
        self.preview_lbl = ttk.Label(self.preview_frame)
        self.preview_lbl.pack(anchor="center")
        
        # Generate a placeholder image
        placeholder = tk.PhotoImage(width=1, height=1)
        self.default_img = placeholder
        self.preview_lbl.configure(image=self.default_img)
        
        # Video controls frame (will be populated when needed)
        self.video_controls = ttk.Frame(self.preview_frame)
        
        # Create a horizontal separator
        ttk.Separator(right_frame, orient="horizontal").pack(fill="x", pady=10)

        # –– READ‑ONLY info bar –––––––––––––––––––––––––––––––––––––––––––––––
        info_frame = ttk.LabelFrame(right_frame, text="File Information", padding=10)
        info_frame.pack(fill="x", pady=(0, 10))
        
        info_grid = ttk.Frame(info_frame)
        info_grid.pack(fill="x")

        # File name
        ttk.Label(info_grid, text="File:", width=12, anchor="e").grid(row=0, column=0, sticky="w", pady=2)
        self.fn_lbl = ttk.Label(info_grid, width=60, anchor="w")
        self.fn_lbl.grid(row=0, column=1, sticky="w", pady=2)

        # ID
        ttk.Label(info_grid, text="ID:", width=12, anchor="e").grid(row=1, column=0, sticky="w", pady=2)
        self.id_lbl = ttk.Label(info_grid, width=60, anchor="w")
        self.id_lbl.grid(row=1, column=1, sticky="w", pady=2)

        # Date taken
        ttk.Label(info_grid, text="Date Taken:", width=12, anchor="e").grid(row=2, column=0, sticky="w", pady=2)
        self.date_lbl = ttk.Label(info_grid, width=60, anchor="w")
        self.date_lbl.grid(row=2, column=1, sticky="w", pady=2)

        # Location coordinates / Rating Key (dynamic based on media type)
        ttk.Label(info_grid, text="Info:", width=12, anchor="e").grid(row=3, column=0, sticky="w", pady=2)
        self.loc_lbl = ttk.Label(info_grid, width=60, anchor="w")
        self.loc_lbl.grid(row=3, column=1, sticky="w", pady=2)
        
        # Additional music-specific fields (will be hidden for non-music files)
        self.music_info_labels = {}
        self.music_info_values = {}
        
        # Artist field
        self.music_info_labels["artist"] = ttk.Label(info_grid, text="Artist:", width=12, anchor="e")
        self.music_info_values["artist"] = ttk.Label(info_grid, width=60, anchor="w")
        
        # Album field  
        self.music_info_labels["album"] = ttk.Label(info_grid, text="Album:", width=12, anchor="e")
        self.music_info_values["album"] = ttk.Label(info_grid, width=60, anchor="w")
        
        # Date Original field
        self.music_info_labels["date_orig"] = ttk.Label(info_grid, text="Date Original:", width=12, anchor="e")
        self.music_info_values["date_orig"] = ttk.Label(info_grid, width=60, anchor="w")
        
        # File Path field
        self.music_info_labels["filepath"] = ttk.Label(info_grid, text="File Path:", width=12, anchor="e")
        self.music_info_values["filepath"] = ttk.Label(info_grid, width=60, anchor="w")
        
        # Play button frame (will be shown only for music)
        self.play_button_frame = ttk.Frame(info_grid)
        self.play_button = ttk.Button(self.play_button_frame, text="🎵 Play with System Player", 
                                     command=self.play_current_music_file)
        self.play_button.pack(side="left")

        # Create container for form and buttons to manage layout properly
        content_container = ttk.Frame(right_frame)
        content_container.pack(fill="both", expand=True)

        # –– DYNAMIC EDITABLE form with scrolling –––––––––––––––––––––––––––––––––––––––––––––
        form_outer_frame = ttk.LabelFrame(content_container, text="Edit Metadata", padding=10)
        form_outer_frame.pack(fill="both", expand=True, pady=(0, 5))
        
        # Create scrollable canvas for the form
        self.form_canvas = tk.Canvas(form_outer_frame)
        form_scrollbar = ttk.Scrollbar(form_outer_frame, orient="vertical", command=self.form_canvas.yview)
        self.form_frame = ttk.Frame(self.form_canvas)
        
        # Configure scrolling
        self.form_frame.bind("<Configure>", lambda e: self.form_canvas.configure(scrollregion=self.form_canvas.bbox("all")))
        self.form_canvas.create_window((0, 0), window=self.form_frame, anchor="nw")
        self.form_canvas.configure(yscrollcommand=form_scrollbar.set)
        
        # Pack scrollable components
        self.form_canvas.pack(side="left", fill="both", expand=True)
        form_scrollbar.pack(side="right", fill="y")
        
        # Enable mouse wheel scrolling
        def _on_mousewheel(event):
            if self.form_canvas.winfo_exists():
                self.form_canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        
        self.form_canvas.bind("<MouseWheel>", _on_mousewheel)  # Windows/Mac
        self.form_canvas.bind("<Button-4>", lambda e: self.form_canvas.yview_scroll(-1, "units"))  # Linux
        self.form_canvas.bind("<Button-5>", lambda e: self.form_canvas.yview_scroll(1, "units"))   # Linux
        
        # This will be populated dynamically based on media type
        self.current_form = None
        self.current_media_type = None

        # Add separator line above buttons for visual clarity
        ttk.Separator(content_container, orient="horizontal").pack(fill="x", pady=(5, 5))

        # –– STICKY action buttons (always visible at bottom) ––––––––––––––––––––––––––––––––––
        btns = ttk.Frame(content_container, padding=(0, 8, 0, 5))
        btns.pack(side="bottom", fill="x", pady=(0, 0))  # Explicit bottom placement with no expand
        
        # Navigation buttons
        nav_frame = ttk.Frame(btns)
        nav_frame.pack(side="left")
        ttk.Button(nav_frame, text="Previous", command=self.on_previous).pack(side="left", padx=(0, 5))
        ttk.Button(nav_frame, text="Next", command=self.on_next).pack(side="left")
        
        # Save button with accent style
        self.style.configure("Accent.TButton", background=self.accent_color)
        ttk.Button(btns, text="Save Changes", command=self.on_save, style="Accent.TButton").pack(side="right")

        # Delete button
        ttk.Button(btns, text="Delete",
                   command=self.delete_selected_image).pack(side="right", padx=(0, 8))

        # Edit All Fields button
        ttk.Button(btns, text="Edit All Fields",
                   command=self.open_full_editor).pack(side="right", padx=(0, 8))

    # --------------------------------------------------------------------
    # Dynamic form creation based on media type
    # --------------------------------------------------------------------
    def create_form_for_media_type(self, media_type: str):
        """Create appropriate form based on media type (photo, video, music)."""
        # Clear existing form
        if self.current_form:
            self.current_form.destroy()
        
        self.current_form = ttk.Frame(self.form_frame)
        self.current_form.pack(fill="both", expand=True)
        self.current_media_type = media_type
        
        if media_type == "music":
            self.create_music_form()
        else:  # photo or video
            self.create_visual_form()
            
        # Update canvas scroll region after creating form
        self.form_frame.update_idletasks()
        self.form_canvas.configure(scrollregion=self.form_canvas.bbox("all"))
    
    def create_music_form(self):
        """Create form for music files with fields in specified order."""
        form = self.current_form
        
        row = 0
        
        # Track Title
        ttk.Label(form, text="Track Title:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.track_title_var = tk.StringVar()
        self.track_title_entry = ttk.Entry(form, textvariable=self.track_title_var, width=60)
        self.track_title_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.track_title_entry)
        row += 1
        
        # Artist
        ttk.Label(form, text="Artist:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.artist_var = tk.StringVar()
        self.artist_entry = ttk.Entry(form, textvariable=self.artist_var, width=60)
        self.artist_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.artist_entry)
        row += 1
        
        # Album
        ttk.Label(form, text="Album:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.album_var = tk.StringVar()
        self.album_entry = ttk.Entry(form, textvariable=self.album_var, width=60)
        self.album_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.album_entry)
        row += 1
        
        # Moods
        ttk.Label(form, text="Moods:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.moods_var = tk.StringVar()
        self.moods_entry = ttk.Entry(form, textvariable=self.moods_var, width=60)
        self.moods_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.moods_entry)
        row += 1
        
        # Genre
        ttk.Label(form, text="Genre:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.genre_var = tk.StringVar()
        self.genre_entry = ttk.Entry(form, textvariable=self.genre_var, width=60)
        self.genre_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.genre_entry)
        row += 1
        
        # Year
        ttk.Label(form, text="Year:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.year_var = tk.StringVar()
        self.year_entry = ttk.Entry(form, textvariable=self.year_var, width=60)
        self.year_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.year_entry)
        row += 1
        
        # Track Number
        ttk.Label(form, text="Track Number:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.track_number_var = tk.StringVar()
        self.track_number_entry = ttk.Entry(form, textvariable=self.track_number_var, width=60)
        self.track_number_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.track_number_entry)
        row += 1
        
        # Rating Key
        ttk.Label(form, text="Rating Key:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.rating_key_var = tk.StringVar()
        self.rating_key_entry = ttk.Entry(form, textvariable=self.rating_key_var, width=60)
        self.rating_key_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.rating_key_entry)
        row += 1
        
        # File Path
        ttk.Label(form, text="File Path:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.file_path_var = tk.StringVar()
        self.file_path_entry = ttk.Entry(form, textvariable=self.file_path_var, width=60)
        self.file_path_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.file_path_entry)
        row += 1
        
        # Album Summary
        ttk.Label(form, text="Album Summary:", width=15, anchor="ne").grid(row=row, column=0, sticky="ne", pady=5)
        self.album_summary_txt = tk.Text(form, width=60, height=3, wrap="word")
        self.album_summary_txt.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.album_summary_txt)
        row += 1
        
        # Artist Summary
        ttk.Label(form, text="Artist Summary:", width=15, anchor="ne").grid(row=row, column=0, sticky="ne", pady=5)
        self.artist_summary_txt = tk.Text(form, width=60, height=3, wrap="word")
        self.artist_summary_txt.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.artist_summary_txt)
        row += 1
        
        # Summary
        ttk.Label(form, text="Summary:", width=15, anchor="ne").grid(row=row, column=0, sticky="ne", pady=5)
        self.summary_txt = tk.Text(form, width=60, height=3, wrap="word")
        self.summary_txt.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.summary_txt)
        row += 1
        
        # Bitrate
        ttk.Label(form, text="Bitrate:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.bitrate_var = tk.StringVar()
        self.bitrate_entry = ttk.Entry(form, textvariable=self.bitrate_var, width=60)
        self.bitrate_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.bitrate_entry)
        row += 1
        
        # Codec
        ttk.Label(form, text="Codec:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.codec_var = tk.StringVar()
        self.codec_entry = ttk.Entry(form, textvariable=self.codec_var, width=60)
        self.codec_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.codec_entry)
        row += 1
        
        # Channels
        ttk.Label(form, text="Channels:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.channels_var = tk.StringVar()
        self.channels_entry = ttk.Entry(form, textvariable=self.channels_var, width=60)
        self.channels_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.channels_entry)
        row += 1
        
        # Container
        ttk.Label(form, text="Container:", width=15, anchor="e").grid(row=row, column=0, sticky="w", pady=5)
        self.container_var = tk.StringVar()
        self.container_entry = ttk.Entry(form, textvariable=self.container_var, width=60)
        self.container_entry.grid(row=row, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.container_entry)
        
        form.columnconfigure(1, weight=1)
    
    def create_visual_form(self):
        """Create form for photos and videos."""
        form = self.current_form
        
        # Keywords
        ttk.Label(form, text="Keywords:", width=12, anchor="e").grid(row=0, column=0, sticky="w", pady=5)
        self.kw_var = tk.StringVar()
        self.kw_entry = ttk.Entry(form, textvariable=self.kw_var, width=60)
        self.kw_entry.grid(row=0, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.kw_entry)
        ttk.Label(form, text="(comma separated)").grid(row=0, column=2, sticky="w", padx=5, pady=5)

        # Location name
        ttk.Label(form, text="Location name:", width=12, anchor="e").grid(row=1, column=0, sticky="w", pady=5)
        self.loc_var = tk.StringVar()
        self.loc_entry = ttk.Entry(form, textvariable=self.loc_var, width=60)
        self.loc_entry.grid(row=1, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.loc_entry)

        # People
        ttk.Label(form, text="People:", width=12, anchor="e").grid(row=2, column=0, sticky="w", pady=5)
        self.people_var = tk.StringVar()
        self.people_entry = ttk.Entry(form, textvariable=self.people_var, width=60)
        self.people_entry.grid(row=2, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.people_entry)
        ttk.Label(form, text="(comma separated)").grid(row=2, column=2, sticky="w", padx=5, pady=5)

        # Labels
        ttk.Label(form, text="Labels:", width=12, anchor="e").grid(row=3, column=0, sticky="w", pady=5)
        self.labels_var = tk.StringVar()
        self.labels_entry = ttk.Entry(form, textvariable=self.labels_var, width=60)
        self.labels_entry.grid(row=3, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.labels_entry)
        ttk.Label(form, text="(comma separated)").grid(row=3, column=2, sticky="w", padx=5, pady=5)

        # Description
        ttk.Label(form, text="Description:", width=12, anchor="ne").grid(row=4, column=0, sticky="ne", pady=5)
        self.desc_txt = tk.Text(form, width=60, height=4, wrap="word")
        self.desc_txt.grid(row=4, column=1, sticky="we", pady=5)
        self.apply_copy_paste_bindings(self.desc_txt)
        
        # Add a scrollbar for description
        desc_sb = ttk.Scrollbar(form, orient="vertical", command=self.desc_txt.yview)
        self.desc_txt.configure(yscrollcommand=desc_sb.set)
        desc_sb.grid(row=4, column=2, sticky="ns", pady=5)

        form.columnconfigure(1, weight=1)

    def load_music_fields(self, row):
        """Load music-specific fields from database row with proper field mapping."""
        # Map database fields to form variables
        if hasattr(self, 'track_title_var'):
            # Track title comes from description field
            self.track_title_var.set(row["description"] if row["description"] else "")
        if hasattr(self, 'artist_var'):
            self.artist_var.set(row["artist"] if row["artist"] and row["artist"] != "None" else "")
        if hasattr(self, 'album_var'):
            self.album_var.set(row["album"] if row["album"] and row["album"] != "None" else "")
        if hasattr(self, 'moods_var'):
            self.moods_var.set(row["moods"] if row["moods"] else "")
        if hasattr(self, 'genre_var'):
            self.genre_var.set(row["genre"] if row["genre"] else "")
        if hasattr(self, 'year_var'):
            year_val = row["year"]
            self.year_var.set(str(year_val) if year_val else "")
        if hasattr(self, 'track_number_var'):
            track_num = row["track_number"]
            self.track_number_var.set(str(track_num) if track_num else "")
        if hasattr(self, 'rating_key_var'):
            self.rating_key_var.set(row["rating_key"] if row["rating_key"] else "")
        if hasattr(self, 'file_path_var'):
            self.file_path_var.set(row["file_path"] if row["file_path"] else "")
        
        # Text areas for summaries
        if hasattr(self, 'album_summary_txt'):
            self.album_summary_txt.delete("1.0", "end")
            self.album_summary_txt.insert("end", row["album_summary"] if row["album_summary"] else "")
        if hasattr(self, 'artist_summary_txt'):
            self.artist_summary_txt.delete("1.0", "end")
            self.artist_summary_txt.insert("end", row["artist_summary"] if row["artist_summary"] else "")
        if hasattr(self, 'summary_txt'):
            self.summary_txt.delete("1.0", "end")
            self.summary_txt.insert("end", row["summary"] if row["summary"] else "")
            
        # Technical fields
        if hasattr(self, 'bitrate_var'):
            bitrate_val = row["bitrate"]
            self.bitrate_var.set(str(bitrate_val) if bitrate_val else "")
        if hasattr(self, 'codec_var'):
            self.codec_var.set(row["codec"] if row["codec"] else "")
        if hasattr(self, 'channels_var'):
            self.channels_var.set(row["channels"] if row["channels"] else "")
        if hasattr(self, 'container_var'):
            self.container_var.set(row["container"] if row["container"] else "")

    def load_visual_fields(self, row):
        """Load visual media fields from database row."""
        self.kw_var.set(", ".join(self._safe_json_list(row["keywords"])))
        self.loc_var.set(self._safe_json_str(row["location_name"]))
        self.people_var.set(", ".join(self._safe_json_list(row["people"])))
        self.labels_var.set(", ".join(self._safe_json_list(row["labels"])))
        
        self.desc_txt.delete("1.0", "end")
        self.desc_txt.insert("end", row["description"] or "")

    def setup_music_preview(self, music_path: Path, row):
        """Set up preview area for music files - show album art if available."""
        # Clean up any existing components
        self.stop_video()
        if self.video_player:
            self.video_player.destroy()
            self.video_player = None
        if self.video_frame:
            self.video_frame.destroy()
            self.video_frame = None
        
        # Clear video controls and click handlers
        self.video_controls.pack_forget()
        for widget in self.video_controls.winfo_children():
            widget.destroy()
        self.preview_lbl.unbind("<Button-1>")
        self.preview_lbl.configure(cursor="")
        
        # Hide existing image frame if it exists
        if hasattr(self, 'image_frame') and self.image_frame:
            self.image_frame.pack_forget()
            # Clear image controls
            if hasattr(self, 'image_controls'):
                for widget in self.image_controls.winfo_children():
                    widget.destroy()
        
        # Show the main preview label with album art or placeholder
        self.preview_lbl.pack(anchor="center")
        
        # Store current music row for album art updates
        self.current_music_row = row
        self.current_music_path = music_path
        
        # Try to display album art or show placeholder
        self.display_album_art_or_placeholder(row, music_path)
        
        # Add music controls
        if not hasattr(self, 'music_controls'):
            self.music_controls = ttk.Frame(self.preview_frame)
        else:
            # Clear existing controls
            for widget in self.music_controls.winfo_children():
                widget.destroy()
        
        self.music_controls.pack(fill="x", pady=5)
        
        # Play Audio button
        play_audio_btn = ttk.Button(self.music_controls, text="🎵 Play Audio", 
                                   command=lambda: self.play_audio_file(music_path))
        play_audio_btn.pack(side="left", padx=5)
        
        # Music info
        info_label = ttk.Label(self.music_controls, text=f"Music: {music_path.name}")
        info_label.pack(side="right", padx=5)
        
        print(f"DEBUG: Music controls created for {music_path.name}")

    def display_album_art_or_placeholder(self, row, music_path):
        """Display album art from Plex if available, otherwise show a placeholder with music info."""
        try:
            from PIL import Image, ImageDraw, ImageFont
            from io import BytesIO
            
            # First try to fetch album art from Plex
            album_art_img = None
            rating_key = row["rating_key"]
            
            if rating_key:
                try:
                    album_art_img = self.fetch_plex_album_art(rating_key)
                except Exception as e:
                    print(f"Warning: Failed to fetch album art from Plex for rating_key {rating_key}: {e}")
            
            # If we got album art from Plex, use it
            if album_art_img:
                # Resize to fit our display area (400x300)
                album_art_img = album_art_img.resize((400, 300), Image.Resampling.LANCZOS)
                self.tk_img = ImageTk.PhotoImage(album_art_img)
                self.preview_lbl.configure(image=self.tk_img, text="")
                return
            
            # Fallback: Create placeholder image
            img = Image.new('RGB', (400, 300), color='lightsteelblue')
            draw = ImageDraw.Draw(img)
            
            # Try to use a default font
            try:
                font = ImageFont.truetype("Arial.ttf", 16)
                title_font = ImageFont.truetype("Arial.ttf", 20)
                small_font = ImageFont.truetype("Arial.ttf", 12)
            except:
                font = ImageFont.load_default()
                title_font = font
                small_font = font
            
            # Get music info from proper database fields
            title = row["description"] if row["description"] else (row["artist"] if row["artist"] and row["artist"] != "None" else "Unknown Title")
            artist = row["artist"] if row["artist"] and row["artist"] != "None" else "Unknown Artist"
            album = row["album"] if row["album"] and row["album"] != "None" else "Unknown Album"
            track_num = row["track_number"] if row["track_number"] else ""
            
            # Draw placeholder with music info
            draw.text((150, 30), "♪ ALBUM ART ♪", fill='navy', font=title_font)
            draw.text((120, 60), "Placeholder", fill='darkblue', font=title_font)
            
            y_pos = 100
            if track_num:
                draw.text((20, y_pos), f"Track: {track_num}", fill='black', font=font)
                y_pos += 25
            draw.text((20, y_pos), f"Title: {title[:40]}", fill='black', font=font)
            y_pos += 25
            draw.text((20, y_pos), f"Artist: {artist[:40]}", fill='black', font=font)
            y_pos += 25
            draw.text((20, y_pos), f"Album: {album[:40]}", fill='black', font=font)
            y_pos += 25
            draw.text((20, y_pos), f"File: {music_path.name[:35]}", fill='gray', font=small_font)
            
            # Convert to PhotoImage
            self.tk_img = ImageTk.PhotoImage(img)
            self.preview_lbl.configure(image=self.tk_img, text="")
            
        except Exception as e:
            # Fallback to text-only
            title = row["description"] if row["description"] else (row["artist"] if row["artist"] and row["artist"] != "None" else "Unknown Title")
            self.preview_lbl.configure(image=self.default_img, 
                                     text=f"♪ Music File ♪\n{title}\n{music_path.name}")

    def fetch_plex_album_art(self, rating_key):
        """Fetch album art from Plex server using rating_key."""
        try:
            from PIL import Image
            from io import BytesIO
            
            # Build the API URL to get track info
            track_url = f"{PLEX_SERVER_URL}/library/metadata/{rating_key}?X-Plex-Token={PLEX_TOKEN}"
            
            # Fetch track metadata
            response = requests.get(track_url, timeout=5)
            response.raise_for_status()
            
            # Parse XML response to find thumb attribute
            import xml.etree.ElementTree as ET
            root = ET.fromstring(response.content)
            
            # Find the Track element and get thumb attribute
            track_elem = root.find('.//Track')
            if track_elem is not None and 'thumb' in track_elem.attrib:
                thumb_path = track_elem.attrib['thumb']
                
                # Build the album art URL
                album_art_url = f"{PLEX_SERVER_URL}{thumb_path}?X-Plex-Token={PLEX_TOKEN}"
                
                # Fetch the album art image
                art_response = requests.get(album_art_url, timeout=10)
                art_response.raise_for_status()
                
                # Load image from response
                image_data = BytesIO(art_response.content)
                return Image.open(image_data)
                
        except Exception as e:
            print(f"Error fetching Plex album art for rating_key {rating_key}: {e}")
            return None
        
        return None

    def update_album_art(self, album_art_image):
        """Update the displayed album art when provided with an image."""
        try:
            if hasattr(self, 'current_music_row') and self.current_music_row:
                from PIL import Image, ImageTk
                
                # Resize the provided album art to fit the display
                album_art_image = album_art_image.resize((400, 300), Image.Resampling.LANCZOS)
                
                # Convert to PhotoImage
                self.tk_img = ImageTk.PhotoImage(album_art_image)
                self.preview_lbl.configure(image=self.tk_img, text="")
                
                print("Album art updated successfully")
        except Exception as e:
            print(f"Error updating album art: {e}")
            # Fall back to placeholder if there's an error

    # --------------------------------------------------------------------
    # Populate / refresh
    # --------------------------------------------------------------------
    def _populate_tree(self, rows=None):
        """Clear and refill the tree. If rows is None, show all; if it's an empty list, show nothing."""
        # 1) delete existing items
        for child in self.tree.get_children():
            self.tree.delete(child)

        # 2) load all if no rows passed
        if rows is None:
            # Use current filter when loading all records
            filter_type = getattr(self, 'filter_var', None)
            if filter_type:
                current_filter = filter_type.get()
                rows = self.db.search_filtered("", current_filter)
            else:
                rows = self.db.fetch_all()
                current_filter = "All"
        else:
            current_filter = getattr(self, 'filter_var', None)
            if current_filter:
                current_filter = current_filter.get()
            else:
                current_filter = "All"

        # Check if we're in drilled-down mode
        if self.navigation_state["is_drilled_down"]:
            # Don't repopulate during drill-down
            return
            
        # Check if this is a music sub-filter that needs grouped display
        if current_filter in ["Music: Artist", "Music: Album", "Music: Genre", "Music: Mood", "Music: Year"]:
            self._populate_tree_grouped(rows, current_filter)
        else:
            # Reset tree headings for regular view
            self.tree.heading("description", text="File Name")
            self.tree.heading("desc", text="Description")
            # 3) Regular display - insert each row as before
            for r in rows:
                file_name = r["file_name"]
                # Skip records with empty or None file names
                if not file_name or file_name.strip() == "":
                    continue
                desc = r["description"] or ""
                try:
                    self.tree.insert(
                        "",
                        "end",
                        iid=file_name,
                        values=(file_name, desc)
                    )
                except tk.TclError as e:
                    # Skip duplicate items
                    if "already exists" in str(e):
                        print(f"Skipping duplicate item: {file_name}")
                        continue
                    else:
                        raise

    def _populate_tree_grouped(self, rows, filter_type):
        """Populate tree with grouped display for music sub-filters."""
        from collections import defaultdict
        
        # Group the data based on filter type
        groups = defaultdict(list)
        
        for row in rows:
            file_name = row["file_name"]
            if not file_name or file_name.strip() == "":
                continue
                
            # Determine group key based on filter type
            if filter_type == "Music: Artist":
                group_key = row["artist"] if row["artist"] and row["artist"] != "None" else "Unknown Artist"
            elif filter_type == "Music: Album":
                group_key = row["album"] if row["album"] and row["album"] != "None" else "Unknown Album"
            elif filter_type == "Music: Genre":
                group_key = row["genre"] if row["genre"] and row["genre"] != "None" else "Unknown Genre"
            elif filter_type == "Music: Mood":
                moods = row["moods"] if row["moods"] and row["moods"] != "[]" else ""
                if moods:
                    # Handle multiple moods - use first mood as primary group
                    if isinstance(moods, str) and moods.startswith('[') and moods.endswith(']'):
                        # Parse JSON-like mood list
                        try:
                            import json
                            mood_list = json.loads(moods.replace("'", '"'))
                            group_key = mood_list[0] if mood_list else "No Mood"
                        except:
                            group_key = moods
                    else:
                        # Split by comma and take first
                        group_key = moods.split(',')[0].strip() if ',' in moods else moods
                else:
                    group_key = "No Mood"
            elif filter_type == "Music: Year":
                group_key = str(row["year"]) if row["year"] else "Unknown Year"
            else:
                group_key = "Unknown"
            
            groups[group_key].append(row)
        
        # Update tree headings for grouped display
        if filter_type == "Music: Artist":
            self.tree.heading("description", text="Artist")
            self.tree.heading("desc", text="Songs")
        elif filter_type == "Music: Album":
            self.tree.heading("description", text="Album")
            self.tree.heading("desc", text="Songs")
        elif filter_type == "Music: Genre":
            self.tree.heading("description", text="Genre")
            self.tree.heading("desc", text="Songs")
        elif filter_type == "Music: Mood":
            self.tree.heading("description", text="Mood")
            self.tree.heading("desc", text="Songs")
        elif filter_type == "Music: Year":
            self.tree.heading("description", text="Year")
            self.tree.heading("desc", text="Songs")
        
        # Sort groups for display
        sorted_groups = sorted(groups.keys())
        
        # Insert parent groups and their songs
        for group_key in sorted_groups:
            songs = groups[group_key]
            song_count = len(songs)
            
            # Insert parent group
            try:
                parent_id = f"group_{group_key}"
                self.tree.insert(
                    "",
                    "end",
                    iid=parent_id,
                    values=(group_key, f"{song_count} songs"),
                    open=False  # Start collapsed
                )
                
                # Insert songs as children
                for song_row in sorted(songs, key=lambda x: (x["track_number"] if x["track_number"] else 999, x["file_name"])):
                    song_name = song_row["file_name"]
                    track_info = ""
                    if song_row["track_number"]:
                        track_info = f"Track {song_row['track_number']}: "
                    
                    try:
                        self.tree.insert(
                            parent_id,
                            "end", 
                            iid=song_name,
                            values=("", f"{track_info}{song_name}")
                        )
                    except tk.TclError as e:
                        if "already exists" in str(e):
                            # Handle duplicate by using unique ID
                            unique_id = f"{song_name}_{hash(parent_id) % 10000}"
                            self.tree.insert(
                                parent_id,
                                "end",
                                iid=unique_id,
                                values=("", f"{track_info}{song_name}")
                            )
                        else:
                            print(f"Error inserting song {song_name}: {e}")
                            
            except tk.TclError as e:
                print(f"Error inserting group {group_key}: {e}")
            
    # --------------------------------------------------------------------
    # Menu callbacks
    # --------------------------------------------------------------------
    def on_import_master(self):
        path = filedialog.askopenfilename(
            title="Choose master data file (.txt | .jsonl)",
            filetypes=[("JSON Lines", "*.txt *.jsonl"), ("All files", "*")],
        )
        if not path:
            return
        n = self.db.import_master(Path(path))
        self._populate_tree()
        messagebox.showinfo("Import complete", f"{n} records imported.")

    def on_merge_updates(self):
        path = filedialog.askopenfilename(
            title="Choose update file (.jsonl)",
            filetypes=[("JSON Lines", "*.jsonl"), ("All files", "*")],
        )
        if not path:
            return
        n = self.db.merge_updates(Path(path))
        self._populate_tree()
        messagebox.showinfo("Merge complete", f"{n} records updated.")

    def on_export_jsonl(self):
        out_dir = filedialog.askdirectory(title="Export to directory")
        if not out_dir:
            return
        num_files = self.db.export_jsonl(Path(out_dir))
        messagebox.showinfo("Export complete", f"Wrote {num_files} chunk(s).")
    
    def on_update_music_data(self):
        """Import and update music data from JSONL files in a directory."""
        self._show_music_data_import_dialog()
        
    def _show_music_data_import_dialog(self):
        """Show dialog to select directory for music data import."""
        dialog = tk.Toplevel(self)
        dialog.title("Update Music Data")
        dialog.geometry("600x250")
        dialog.transient(self)
        dialog.grab_set()
        dialog.resizable(True, False)
        
        # Center the dialog
        dialog.update_idletasks()
        x = (dialog.winfo_screenwidth() // 2) - (dialog.winfo_width() // 2)
        y = (dialog.winfo_screenheight() // 2) - (dialog.winfo_height() // 2)
        dialog.geometry(f"+{x}+{y}")
        
        # Main frame
        main_frame = ttk.Frame(dialog, padding=20)
        main_frame.pack(fill="both", expand=True)
        
        # Title and description
        title_lbl = ttk.Label(main_frame, text="Import Music Metadata", font=('', 12, 'bold'))
        title_lbl.pack(anchor="w", pady=(0, 10))
        
        desc_lbl = ttk.Label(main_frame, text="Select the directory containing music JSONL files to import:")
        desc_lbl.pack(anchor="w", pady=(0, 15))
        
        # Use LabelFrame for better visibility and organization
        dir_label_frame = ttk.LabelFrame(main_frame, text="Directory Selection", padding=10)
        dir_label_frame.pack(fill="x", pady=(0, 20))
        
        # Directory path entry
        ttk.Label(dir_label_frame, text="Path:").grid(row=0, column=0, sticky="w", padx=(0, 5))
        self.music_dir_var = tk.StringVar(value="vector_export/music")
        dir_entry = ttk.Entry(dir_label_frame, textvariable=self.music_dir_var, width=50)
        dir_entry.grid(row=0, column=1, sticky="ew", padx=(0, 5))
        
        # Browse button
        browse_btn = ttk.Button(dir_label_frame, text="Browse...", command=self._browse_music_directory)
        browse_btn.grid(row=0, column=2, sticky="w")
        
        # Configure column weights
        dir_label_frame.columnconfigure(1, weight=1)
        
        # Button frame
        btn_frame = ttk.Frame(main_frame)
        btn_frame.pack(fill="x")
        
        # Import button
        import_btn = ttk.Button(btn_frame, text="Import Music Data", 
                               command=lambda: self._import_music_data(dialog))
        import_btn.pack(side="right", padx=(10, 0))
        
        # Cancel button  
        cancel_btn = ttk.Button(btn_frame, text="Cancel", command=dialog.destroy)
        cancel_btn.pack(side="right")
        
    def _browse_music_directory(self):
        """Browse for music data directory."""
        directory = filedialog.askdirectory(title="Select Music Data Directory")
        if directory:
            self.music_dir_var.set(directory)
            
    def _import_music_data(self, dialog):
        """Import music data from the selected directory."""
        import_dir = Path(self.music_dir_var.get())
        
        if not import_dir.exists():
            messagebox.showerror("Error", f"Directory does not exist: {import_dir}")
            return
            
        # Find JSONL files
        jsonl_files = list(import_dir.glob("*.jsonl"))
        
        if not jsonl_files:
            messagebox.showerror("Error", f"No JSONL files found in: {import_dir}")
            return
            
        dialog.destroy()
        
        # Show progress dialog
        self._import_music_files(jsonl_files)
    
    def _import_music_files(self, jsonl_files):
        """Import music data from JSONL files with progress dialog."""
        import json
        
        # Create progress dialog
        progress_dialog = tk.Toplevel(self)
        progress_dialog.title("Importing Music Data...")
        progress_dialog.geometry("400x150")
        progress_dialog.transient(self)
        progress_dialog.grab_set()
        
        # Center the dialog
        progress_dialog.update_idletasks()
        x = (progress_dialog.winfo_screenwidth() // 2) - (progress_dialog.winfo_width() // 2)
        y = (progress_dialog.winfo_screenheight() // 2) - (progress_dialog.winfo_height() // 2)
        progress_dialog.geometry(f"+{x}+{y}")
        
        # Progress frame
        progress_frame = ttk.Frame(progress_dialog, padding=20)
        progress_frame.pack(fill="both", expand=True)
        
        # Status label
        status_label = ttk.Label(progress_frame, text="Preparing to import...")
        status_label.pack(pady=(0, 10))
        
        # Progress bar
        progress_bar = ttk.Progressbar(progress_frame, mode='determinate')
        progress_bar.pack(fill="x", pady=(0, 10))
        
        # Stats labels
        stats_label = ttk.Label(progress_frame, text="Files: 0 | Records: 0 | Updated: 0")
        stats_label.pack()
        
        # Process files
        total_files = len(jsonl_files)
        total_records = 0
        updated_count = 0
        
        progress_bar['maximum'] = total_files
        
        try:
            cursor = self.db.conn.cursor()
            
            # Begin transaction
            self.db.conn.execute("BEGIN TRANSACTION")
            
            errors_encountered = []
            successful_updates = 0
            
            for file_idx, jsonl_file in enumerate(jsonl_files):
                # Update status
                status_label.config(text=f"Processing: {jsonl_file.name}")
                progress_dialog.update()
                
                try:
                    with open(jsonl_file, 'r', encoding='utf-8') as f:
                        for line_num, line in enumerate(f, 1):
                            if line.strip():
                                try:
                                    data = json.loads(line)
                                    total_records += 1
                                    
                                    # Extract metadata from multiple sources
                                    metadata = data.get('metadata', {})
                                    tech_info = data.get('tech', [{}])[0] if data.get('tech') else {}
                                    text_data = data.get('text', '')
                                    audio_common = metadata.get('audio_common', {})
                                    
                                    # Parse text field for additional data
                                    text_fields = self._parse_text_field(text_data)
                                    
                                    # Get file path to match against database
                                    file_paths = data.get('files', [])
                                    if not file_paths:
                                        # Try getting from tech array first
                                        tech_info_list = data.get('tech', [])
                                        if tech_info_list and len(tech_info_list) > 0:
                                            parts = tech_info_list[0].get('parts', [])
                                            if parts and len(parts) > 0:
                                                file_path = parts[0].get('file', '')
                                                if file_path:
                                                    file_paths = [file_path]
                                        
                                        if not file_paths:
                                            print(f"DEBUG: No files found in record {line_num} of {jsonl_file.name}")
                                            continue
                                        
                                    file_path = file_paths[0]
                                    file_name = Path(file_path).name
                                    
                                    print(f"DEBUG: Looking for file: {file_name} (path: {file_path})")
                                    
                                    # Extract year from addedAt if available
                                    added_at = audio_common.get('addedAt', '')
                                    year_from_added = ''
                                    if added_at:
                                        try:
                                            year_from_added = added_at.split('-')[0]
                                        except:
                                            pass
                                    
                                    # Prepare update data with comprehensive field mapping
                                    update_data = {
                                        'artist': metadata.get('artist', '') or text_fields.get('Artist', ''),
                                        'album': metadata.get('album', '') or text_fields.get('Album', ''),
                                        'moods': ', '.join(metadata.get('moods', [])) or text_fields.get('Moods', ''),
                                        'year': str(metadata.get('year', '')) or text_fields.get('Year', '') or year_from_added,
                                        'album_summary': metadata.get('album_summary', '') or text_fields.get('AlbumSummary', ''),
                                        'artist_summary': metadata.get('artist_summary', '') or text_fields.get('ArtistSummary', ''),
                                        'summary': metadata.get('summary', '') or audio_common.get('summary', ''),
                                        'bitrate': f"{tech_info.get('bitrate_kbps', '')}kbps" if tech_info.get('bitrate_kbps') else text_fields.get('bitrate', ''),
                                        'codec': tech_info.get('audioCodec', '') or text_fields.get('codec', ''),
                                        'channels': 'Stereo' if tech_info.get('audioChannels') == 2 else 'Mono' if tech_info.get('audioChannels') == 1 else text_fields.get('ch', ''),
                                        'container': tech_info.get('container', '') or text_fields.get('container', ''),
                                        'genre': text_fields.get('Genre', ''),
                                        'duration': text_fields.get('Duration_s', '') or str(metadata.get('duration_s', '')),
                                        'description': metadata.get('title', '') or text_fields.get('Track', ''),
                                        'date_original': added_at.split('T')[0] if 'T' in added_at else ''
                                    }
                                    
                                    # Get the rating key (which corresponds to database ID)
                                    rating_key = metadata.get('ratingKey', None) or metadata.get('rating_key', None)
                                    
                                    if rating_key:
                                        # Match by rating key (most reliable)
                                        cursor.execute("SELECT id FROM media WHERE id = ? AND media_type = 'music'", (str(rating_key),))
                                        result = cursor.fetchone()
                                        print(f"DEBUG: Looking for ratingKey/ID: {rating_key}")
                                    else:
                                        # Fallback: try to match by file name first, then by file path
                                        cursor.execute("SELECT id FROM media WHERE file_name = ? AND media_type = 'music'", (file_name,))
                                        result = cursor.fetchone()
                                        
                                        if not result:
                                            # Try matching by file path
                                            cursor.execute("SELECT id FROM media WHERE file_path = ? AND media_type = 'music'", (file_path,))
                                            result = cursor.fetchone()
                                        
                                        print(f"DEBUG: Fallback matching by filename: {file_name}")
                                    
                                    if result:
                                        # Filter out empty values to avoid overwriting existing data
                                        filtered_data = {k: v for k, v in update_data.items() if v and v.strip()}
                                        
                                        if filtered_data:
                                            set_clause = ', '.join([f"{k} = ?" for k in filtered_data.keys()])
                                            values = list(filtered_data.values()) + [result[0]]
                                            
                                            cursor.execute(f"""
                                                UPDATE media SET {set_clause}, last_updated = datetime('now')
                                                WHERE id = ?
                                            """, values)
                                            
                                            if cursor.rowcount > 0:
                                                updated_count += 1
                                                successful_updates += 1
                                                print(f"DEBUG: Updated record for {file_name} with {len(filtered_data)} fields")
                                            else:
                                                print(f"DEBUG: No rows updated for {file_name}")
                                        else:
                                            print(f"DEBUG: No valid data to update for {file_name}")
                                    else:
                                        print(f"DEBUG: No matching record found for {file_name}")
                                        
                                except json.JSONDecodeError as e:
                                    error_msg = f"JSON decode error in {jsonl_file.name} line {line_num}: {e}"
                                    errors_encountered.append(error_msg)
                                    print(f"DEBUG: {error_msg}")
                                    continue
                                except Exception as e:
                                    error_msg = f"Error processing record in {jsonl_file.name} line {line_num}: {e}"
                                    errors_encountered.append(error_msg)
                                    print(f"DEBUG: {error_msg}")
                                    continue
                    
                except Exception as e:
                    error_msg = f"Error reading file {jsonl_file}: {e}"
                    errors_encountered.append(error_msg)
                    print(f"DEBUG: {error_msg}")
                    continue
                
                # Update progress
                progress_bar['value'] = file_idx + 1
                stats_label.config(text=f"Files: {file_idx + 1}/{total_files} | Records: {total_records} | Updated: {updated_count}")
                progress_dialog.update()
            
            # Commit changes if we have successful updates
            if successful_updates > 0:
                self.db.conn.commit()
                print(f"DEBUG: Successfully committed {successful_updates} updates")
            else:
                self.db.conn.rollback()
                print("DEBUG: No updates to commit, rolling back transaction")
            
            # Close progress dialog
            progress_dialog.destroy()
            
            # Show completion message with error details
            completion_msg = f"Successfully processed {total_files} file(s)\n" \
                           f"Total records: {total_records}\n" \
                           f"Records updated: {updated_count}"
            
            if errors_encountered:
                completion_msg += f"\n\nErrors encountered: {len(errors_encountered)}"
                if len(errors_encountered) <= 3:
                    completion_msg += "\n" + "\n".join(errors_encountered[:3])
                else:
                    completion_msg += f"\n{errors_encountered[0]}\n... and {len(errors_encountered)-1} more (check console for details)"
            
            if updated_count > 0:
                messagebox.showinfo("Import Complete", completion_msg)
            else:
                messagebox.showwarning(
                    "No Updates", 
                    f"Processed {total_files} file(s) and {total_records} records but no updates were made.\n"
                    f"This may indicate:\n"
                    f"• No matching files found in database\n"
                    f"• All fields were empty or already up to date\n"
                    f"• Check console output for detailed debugging info"
                )
            
            # Refresh the tree view
            self._populate_tree()
            
        except Exception as e:
            self.db.conn.rollback()
            progress_dialog.destroy()
            messagebox.showerror("Import Error", f"An error occurred during import: {str(e)}\nTransaction has been rolled back.")
    
    def _parse_text_field(self, text_data):
        """Parse the text field to extract music metadata."""
        fields = {}
        if not text_data:
            return fields
            
        lines = text_data.split('\n')
        for line in lines:
            line = line.strip()
            if ':' in line:
                key, value = line.split(':', 1)
                key = key.strip()
                value = value.strip()
                
                # Handle special cases
                if key == 'Tech' and '=' in value:
                    # Parse tech info like "bitrate=128kbps codec=mp3 ch=2 container=mp3"
                    tech_parts = value.split()
                    for part in tech_parts:
                        if '=' in part:
                            tech_key, tech_value = part.split('=', 1)
                            fields[tech_key] = tech_value
                elif value and value != 'None':
                    fields[key] = value
                    
        return fields

    def on_fix_file_paths(self):
        """Fix file_path entries for currently filtered items with custom base path."""
        # Get currently displayed items
        displayed_items = []
        for child in self.tree.get_children():
            displayed_items.append(child)  # child is the file_name (iid)
        
        if not displayed_items:
            messagebox.showwarning("Fix File Paths", "No items currently displayed to update.")
            return
        
        # Get current filter info for the dialog
        current_filter = self.filter_var.get()
        search_text = self.search_var.get().strip()
        filter_info = f"Current filter: {current_filter}"
        if search_text:
            filter_info += f"\nSearch: '{search_text}'"
        
        # Create custom dialog for path input
        dialog = tk.Toplevel(self)
        dialog.title("Fix File Paths")
        dialog.geometry("500x300")
        dialog.transient(self)
        dialog.grab_set()
        dialog.resizable(True, False)
        
        # Info about what will be updated
        info_frame = ttk.Frame(dialog, padding=10)
        info_frame.pack(fill="x")
        
        ttk.Label(info_frame, text=f"This will update file paths for {len(displayed_items)} items").pack(anchor="w")
        ttk.Label(info_frame, text=filter_info).pack(anchor="w", pady=(5,0))
        
        # Path input
        path_frame = ttk.Frame(dialog, padding=10)
        path_frame.pack(fill="x")
        
        ttk.Label(path_frame, text="Base directory path:").pack(anchor="w")
        
        path_var = tk.StringVar()
        # Default to photos_export for photos/videos, current directory for music
        if current_filter in ["Photos", "Videos"]:
            path_var.set(str(PHOTOS_DIR))
        else:
            path_var.set(os.getcwd())
            
        path_entry = ttk.Entry(path_frame, textvariable=path_var, width=60)
        path_entry.pack(fill="x", pady=(5,0))
        
        ttk.Button(path_frame, text="Browse...", 
                  command=lambda: self._browse_directory(path_var)).pack(anchor="w", pady=(5,0))
        
        # Buttons
        btn_frame = ttk.Frame(dialog, padding=10)
        btn_frame.pack(fill="x")
        
        result = {"cancelled": True}
        
        def apply_fix():
            base_path = path_var.get().strip()
            if not base_path:
                messagebox.showwarning("Fix File Paths", "Please enter a base directory path.")
                return
            if not Path(base_path).is_dir():
                messagebox.showwarning("Fix File Paths", "Please enter a valid directory path.")
                return
            
            try:
                updated = self.db.fix_file_paths(base_path, displayed_items)
                result["cancelled"] = False
                result["updated"] = updated
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to fix file paths: {e}")
        
        ttk.Button(btn_frame, text="Cancel", command=dialog.destroy).pack(side="right")
        ttk.Button(btn_frame, text="Apply", command=apply_fix).pack(side="right", padx=(0,10))
        
        # Wait for dialog to close
        dialog.wait_window()
        
        if not result["cancelled"]:
            messagebox.showinfo("Fix Complete", 
                              f"Updated {result['updated']} file path(s) to use base directory:\n{path_var.get()}")
            # Refresh the current record if one is loaded
            if self.current_file:
                self.load_record(self.current_file)
    
    def _browse_directory(self, path_var):
        """Browse for directory and update the path variable."""
        directory = filedialog.askdirectory(title="Select Base Directory", 
                                           initialdir=path_var.get())
        if directory:
            path_var.set(directory)

    # --------------------------------------------------------------------
    # Tree / search callbacks
    # --------------------------------------------------------------------
    def on_search_change(self, *args):
        """Handle live search as user types with debouncing."""
        # Cancel previous timer if it exists
        if self.search_timer:
            self.root.after_cancel(self.search_timer)
        
        # Schedule new search after 300ms delay
        self.search_timer = self.root.after(300, self.perform_search)
    
    def perform_search(self):
        """Perform the actual search."""
        q = self.search_var.get().strip()
        filter_type = self.filter_var.get()
        
        # If search query is empty, restore original filter view
        if not q:
            self.clear_search()
            return
        
        # Store pre-search state for back button functionality
        if not hasattr(self, 'pre_search_state') or not self.pre_search_state.get('in_search'):
            self.pre_search_state = {
                'in_search': True,
                'filter_type': filter_type,
                'navigation_state': self.navigation_state.copy()
            }
            # Show back button during search
            self.back_button.pack(side="left", padx=(10, 0))
        
        # Reset drill-down state during search
        self.navigation_state = {
            "is_drilled_down": False,
            "parent_filter": None,
            "selected_category": None,
            "category_songs": None
        }
        
        # Perform search within current filter
        if filter_type in ["Music: Artist", "Music: Album", "Music: Genre", "Music: Mood", "Music: Year"]:
            self.perform_grouped_search(q, filter_type)
        else:
            # Regular search for non-grouped filters
            rows = self.db.search_filtered(q, filter_type)
            self._populate_tree(rows)
        
        self.search_timer = None
    
    def perform_grouped_search(self, query, filter_type):
        """Perform search within grouped display (jump to matching groups)."""
        # Get all rows for the filter type
        all_rows = self.db.search_filtered("", filter_type)
        
        # Group the data and find matching groups
        from collections import defaultdict
        groups = defaultdict(list)
        matching_groups = []
        query_lower = query.lower()
        
        for row in all_rows:
            file_name = row["file_name"]
            if not file_name or file_name.strip() == "":
                continue
                
            # Determine group key based on filter type
            if filter_type == "Music: Artist":
                group_key = row["artist"] if row["artist"] and row["artist"] != "None" else "Unknown Artist"
            elif filter_type == "Music: Album":
                group_key = row["album"] if row["album"] and row["album"] != "None" else "Unknown Album"
            elif filter_type == "Music: Genre":
                group_key = row["genre"] if row["genre"] and row["genre"] != "None" else "Unknown Genre"
            elif filter_type == "Music: Mood":
                moods = row["moods"] if row["moods"] and row["moods"] != "[]" else ""
                if moods:
                    if isinstance(moods, str) and moods.startswith('[') and moods.endswith(']'):
                        try:
                            import json
                            mood_list = json.loads(moods.replace("'", '"'))
                            group_key = mood_list[0] if mood_list else "No Mood"
                        except:
                            group_key = moods
                    else:
                        group_key = moods.split(',')[0].strip() if ',' in moods else moods
                else:
                    group_key = "No Mood"
            elif filter_type == "Music: Year":
                group_key = str(row["year"]) if row["year"] else "Unknown Year"
            else:
                group_key = "Unknown"
            
            groups[group_key].append(row)
            
            # Check if group matches search query
            if query_lower in group_key.lower() and group_key not in matching_groups:
                matching_groups.append(group_key)
        
        # Populate tree with all groups but highlight/expand matching ones
        self.populate_tree_with_search_highlighting(groups, filter_type, matching_groups, query)
    
    def populate_tree_with_search_highlighting(self, groups, filter_type, matching_groups, query):
        """Populate tree with search highlighting and jump to first match."""
        # Clear tree
        for child in self.tree.get_children():
            self.tree.delete(child)
        
        # Update tree headings for grouped display
        if filter_type == "Music: Artist":
            self.tree.heading("description", text="Artist")
            self.tree.heading("desc", text="Songs")
        elif filter_type == "Music: Album":
            self.tree.heading("description", text="Album")
            self.tree.heading("desc", text="Songs")
        elif filter_type == "Music: Genre":
            self.tree.heading("description", text="Genre")
            self.tree.heading("desc", text="Songs")
        elif filter_type == "Music: Mood":
            self.tree.heading("description", text="Mood")
            self.tree.heading("desc", text="Songs")
        elif filter_type == "Music: Year":
            self.tree.heading("description", text="Year")
            self.tree.heading("desc", text="Songs")
        
        # Sort groups and find first match for jumping
        sorted_groups = sorted(groups.keys())
        first_match = None
        
        # Insert groups with highlighting
        for group_key in sorted_groups:
            songs = groups[group_key]
            song_count = len(songs)
            
            # Insert parent group
            parent_id = f"group_{group_key}"
            is_match = group_key in matching_groups
            
            try:
                self.tree.insert(
                    "",
                    "end",
                    iid=parent_id,
                    values=(group_key, f"{song_count} songs"),
                    open=is_match,  # Expand matching groups
                    tags=('match',) if is_match else ()
                )
                
                if is_match and first_match is None:
                    first_match = parent_id
                
                # Insert songs as children
                for song_row in sorted(songs, key=lambda x: (x["track_number"] if x["track_number"] else 999, x["file_name"])):
                    song_name = song_row["file_name"]
                    track_info = ""
                    if song_row["track_number"]:
                        track_info = f"Track {song_row['track_number']}: "
                    
                    try:
                        self.tree.insert(
                            parent_id,
                            "end", 
                            iid=song_name,
                            values=("", f"{track_info}{song_name}")
                        )
                    except tk.TclError as e:
                        if "already exists" in str(e):
                            unique_id = f"{song_name}_{hash(parent_id) % 10000}"
                            self.tree.insert(
                                parent_id,
                                "end",
                                iid=unique_id,
                                values=("", f"{track_info}{song_name}")
                            )
            except tk.TclError as e:
                if "already exists" not in str(e):
                    print(f"Error inserting group {group_key}: {e}")
        
        # Configure highlighting for matches
        self.tree.tag_configure('match', background='lightblue')
        
        # Jump to first match
        if first_match:
            self.tree.selection_set(first_match)
            self.tree.see(first_match)
    
    def clear_search(self):
        """Clear search and restore original view."""
        if hasattr(self, 'pre_search_state') and self.pre_search_state.get('in_search'):
            # Restore navigation state
            self.navigation_state = self.pre_search_state['navigation_state'].copy()
            self.pre_search_state = {'in_search': False}
            
            # Hide back button if not in drill-down mode
            if not self.navigation_state["is_drilled_down"]:
                self.back_button.pack_forget()
        
        # Restore original filter view
        filter_type = self.filter_var.get()
        rows = self.db.search_filtered("", filter_type)
        self._populate_tree(rows)
    
    def on_search(self, event):
        """Handle Enter key or Search button click."""
        # Cancel any pending search
        if self.search_timer:
            self.root.after_cancel(self.search_timer)
            self.search_timer = None
        
        # Perform immediate search
        self.perform_search()
    
    def on_filter_change(self, event):
        """Handle filter dropdown change."""
        # Reset navigation state when changing filters
        self.navigation_state = {
            "is_drilled_down": False,
            "parent_filter": None,
            "selected_category": None,
            "category_songs": None
        }
        
        # Hide back button when switching filters
        self.back_button.pack_forget()
        
        q = self.search_var.get().strip()
        filter_type = self.filter_var.get()
        rows = self.db.search_filtered(q, filter_type)
        
        # Update Play All button visibility
        self.show_play_all_button()
        
        self._populate_tree(rows)

    def on_tree_select(self, event):
        item = self.tree.selection()
        if not item:
            return
        item_id = item[0]
        
        # Check if this is a group header (starts with "group_") 
        if item_id.startswith("group_"):
            # This is a group header, don't load record
            return
            
        # Handle selection based on current view mode
        if self.navigation_state["is_drilled_down"]:
            # In drilled-down mode, handle unique IDs
            if '_' in item_id and item_id.split('_')[-1].isdigit():
                # This is a unique ID, extract original filename
                file_name = item_id.rsplit('_', 1)[0]
            else:
                file_name = item_id
        else:
            # For child items in grouped view, extract the actual file name
            current_filter = getattr(self, 'filter_var', None)
            if current_filter and current_filter.get() in ["Music: Artist", "Music: Album", "Music: Genre", "Music: Mood", "Music: Year"]:
                # Check if this item has a parent (is a child song)
                parent = self.tree.parent(item_id)
                if parent:
                    # This is a song under a group - use the original file name
                    if item_id.endswith('_' + str(hash(parent) % 10000)):
                        # Handle unique ID case - extract original filename
                        file_name = item_id.rsplit('_', 1)[0]
                    else:
                        file_name = item_id
                else:
                    # This shouldn't happen but fallback to item_id
                    file_name = item_id
            else:
                # Regular view
                file_name = item_id
            
        self.load_record(file_name)

    def on_tree_double_click(self, event):
        """Handle double-click on tree items - drill down into groups or play songs."""
        item = self.tree.selection()
        if not item:
            return
        item_id = item[0]
        
        current_filter = getattr(self, 'filter_var', None)
        if not current_filter:
            return
            
        # Check if we're in drilled-down mode
        if self.navigation_state["is_drilled_down"]:
            # In drill-down mode, double-click plays the song
            self.play_song_from_drill_down(item_id)
            return
        
        # In grouped mode, only handle music sub-filters for drill-down
        if current_filter.get() not in ["Music: Artist", "Music: Album", "Music: Genre", "Music: Mood", "Music: Year"]:
            return
            
        # Check if this is a group header (starts with "group_")
        if item_id.startswith("group_"):
            # Extract the category name from the group ID
            category_name = item_id[6:]  # Remove "group_" prefix
            
            # Get all songs in this category
            filter_type = current_filter.get()
            self.drill_down_into_category(filter_type, category_name)
        else:
            # This is an individual song in the main view - play it with queue management
            print(f"Double-clicking individual song in main view: {item_id}")
            self.play_song_from_main_view(item_id)

    def play_song_from_main_view(self, item_id):
        """Play a song when double-clicked in main view with queue management."""
        try:
            # Extract file name from item ID (handle unique IDs)
            if '_' in item_id and item_id.split('_')[-1].isdigit():
                file_name = item_id.rsplit('_', 1)[0]
            else:
                file_name = item_id
            
            # Get the song record from database
            row = self.db.fetch_one(file_name)
            if not row:
                print(f"Song not found: {file_name}")
                return
                
            # Get file path
            file_path = self.get_music_file_path(row)
            if not file_path:
                print(f"File path not found for: {file_name}")
                return
            
            import sys
            if sys.platform == "darwin":  # macOS - Use smart queue management
                # Check if music is currently playing or we have an active queue
                is_playing = self._check_music_playing_applescript()
                
                if is_playing or self.queue_manager.has_active_queue():
                    # Check if user wants to add to queue or replace it
                    from tkinter import messagebox
                    queue_size = len(self.queue_manager.local_queue)
                    
                    if queue_size > 0:
                        user_choice = messagebox.askyesnocancel(
                            "Add Song to Queue",
                            f"There are {queue_size} songs currently in the queue.\n\n"
                            f"Would you like to:\n"
                            f"• Yes: Replace the current queue with '{file_name}'\n"
                            f"• No: Add '{file_name}' to the end of the current queue\n" 
                            f"• Cancel: Keep the current queue unchanged",
                            icon="question"
                        )
                        
                        if user_choice is None:  # Cancel
                            return
                        elif user_choice is False:  # No - Add to queue
                            print(f"Adding '{file_name}' to existing queue")
                            success = self.queue_manager.smart_add_to_queue(file_path, file_name, self)
                            if not success:
                                print("Smart queue failed, falling back to regular play")
                                self.launch_music_player(file_path, file_name)
                            return
                        # If Yes (True), continue with regular play (replace queue)
                    
                    # Use smart queue management for seamless adding
                    print(f"Using smart queue management for '{file_name}'")
                    success = self.queue_manager.smart_add_to_queue(file_path, file_name, self)
                    if not success:
                        print("Smart queue failed, falling back to regular play")
                        self.launch_music_player(file_path, file_name)
                        self.queue_manager.clear_queue_state()
                else:
                    # No music playing and no active queue - start fresh
                    print(f"Starting fresh playback with '{file_name}'")
                    self.launch_music_player(file_path, file_name)
                    self.queue_manager.clear_queue_state()
            else:
                # Non-macOS platforms - use regular launch behavior
                self.launch_music_player(file_path, file_name)
            
        except Exception as e:
            print(f"Error playing song {item_id}: {e}")
            import traceback
            traceback.print_exc()

    def on_back_button(self):
        """Handle back button click - return to grouped view or clear search."""
        # Check if we're in search mode
        if hasattr(self, 'pre_search_state') and self.pre_search_state.get('in_search'):
            # Clear search and return to original view
            self.search_var.set("")  # Clear search box
            self.clear_search()
            return
        
        # Handle drill-down navigation
        if not self.navigation_state["is_drilled_down"]:
            return
            
        # Restore the grouped view
        parent_filter = self.navigation_state["parent_filter"]
        self.filter_var.set(parent_filter)
        
        # Reset navigation state
        self.navigation_state = {
            "is_drilled_down": False,
            "parent_filter": None,
            "selected_category": None,
            "category_songs": None
        }
        
        # Hide back button and refresh tree
        self.back_button.pack_forget()
        self.show_play_all_button()  # Update Play All button visibility
        self._populate_tree()

    def drill_down_into_category(self, filter_type, category_name):
        """Drill down to show only songs in the selected category."""
        try:
            # Get all songs for the current filter
            all_rows = self.db.search_filtered("", filter_type)
            
            # Filter songs that belong to this category
            category_songs = []
            for row in all_rows:
                if filter_type == "Music: Artist":
                    row_category = row["artist"] if row["artist"] and row["artist"] != "None" else "Unknown Artist"
                elif filter_type == "Music: Album":
                    row_category = row["album"] if row["album"] and row["album"] != "None" else "Unknown Album"
                elif filter_type == "Music: Genre":
                    row_category = row["genre"] if row["genre"] and row["genre"] != "None" else "Unknown Genre"
                elif filter_type == "Music: Mood":
                    moods = row["moods"] if row["moods"] and row["moods"] != "[]" else ""
                    if moods:
                        # Handle multiple moods - use first mood as primary group
                        if isinstance(moods, str) and moods.startswith('[') and moods.endswith(']'):
                            try:
                                import json
                                mood_list = json.loads(moods.replace("'", '"'))
                                row_category = mood_list[0] if mood_list else "No Mood"
                            except:
                                row_category = moods
                        else:
                            row_category = moods.split(',')[0].strip() if ',' in moods else moods
                    else:
                        row_category = "No Mood"
                elif filter_type == "Music: Year":
                    row_category = str(row["year"]) if row["year"] else "Unknown Year"
                else:
                    continue
                    
                if row_category == category_name:
                    category_songs.append(row)
            
            # Update navigation state
            self.navigation_state = {
                "is_drilled_down": True,
                "parent_filter": filter_type,
                "selected_category": category_name,
                "category_songs": category_songs
            }
            
            # Show back button and play all button
            self.back_button.pack(side="left", padx=(10, 0))
            self.show_play_all_button()
            
            # Update filter display and populate with category songs
            self.filter_var.set(f"{filter_type}: {category_name}")
            self._populate_tree_drilled_down(category_songs, filter_type, category_name)
            
        except Exception as e:
            print(f"Error drilling down into category: {e}")
            import traceback
            traceback.print_exc()

    def _populate_tree_drilled_down(self, songs, filter_type, category_name):
        """Populate tree with songs from a specific category."""
        # Clear tree
        for child in self.tree.get_children():
            self.tree.delete(child)
        
        # Update headings for drilled-down view
        category_type = filter_type.split(": ")[1]  # Extract "Artist", "Album", etc.
        self.tree.heading("description", text="Song")
        self.tree.heading("desc", text=f"from {category_type}: {category_name}")
        
        # Sort songs appropriately
        if filter_type in ["Music: Album", "Music: Artist"]:
            # Sort by track number, then by name
            sorted_songs = sorted(songs, key=lambda x: (x["track_number"] if x["track_number"] else 999, x["file_name"]))
        else:
            # Sort by name
            sorted_songs = sorted(songs, key=lambda x: x["file_name"])
        
        # Insert songs
        for song_row in sorted_songs:
            file_name = song_row["file_name"]
            if not file_name or file_name.strip() == "":
                continue
                
            # Build description based on context
            desc_parts = []
            if song_row["track_number"]:
                desc_parts.append(f"Track {song_row['track_number']}")
            if song_row["artist"] and song_row["artist"] != "None" and filter_type != "Music: Artist":
                desc_parts.append(f"by {song_row['artist']}")
            if song_row["album"] and song_row["album"] != "None" and filter_type != "Music: Album":
                desc_parts.append(f"from {song_row['album']}")
            
            description = " • ".join(desc_parts) if desc_parts else ""
            
            try:
                self.tree.insert(
                    "",
                    "end",
                    iid=file_name,
                    values=(file_name, description)
                )
            except tk.TclError as e:
                if "already exists" in str(e):
                    # Handle duplicate by using unique ID
                    unique_id = f"{file_name}_{hash(category_name) % 10000}"
                    self.tree.insert(
                        "",
                        "end",
                        iid=unique_id,
                        values=(file_name, description)
                    )
                else:
                    print(f"Error inserting song {file_name}: {e}")

    def play_song_from_drill_down(self, item_id):
        """Play a song when double-clicked in drill-down mode."""
        try:
            # Extract file name from item ID (handle unique IDs)
            if '_' in item_id and item_id.split('_')[-1].isdigit():
                file_name = item_id.rsplit('_', 1)[0]
            else:
                file_name = item_id
            
            # Get the song record from database
            row = self.db.fetch_one(file_name)
            if not row:
                print(f"Song not found: {file_name}")
                return
                
            # Get file path
            file_path = self.get_music_file_path(row)
            if not file_path:
                print(f"File path not found for: {file_name}")
                return
            
            import sys
            if sys.platform == "darwin":  # macOS - Use smart queue management
                # Check if music is currently playing
                is_playing = self._check_music_playing_applescript()
                
                if is_playing or self.queue_manager.has_active_queue():
                    # Music is playing or we have an active queue - use smart queue management
                    print(f"Using smart queue management for '{file_name}'")
                    success = self.queue_manager.smart_add_to_queue(file_path, file_name, self)
                    if not success:
                        # Fallback to regular play
                        print("Smart queue failed, falling back to regular play")
                        self.launch_music_player(file_path, file_name)
                        # Clear queue state since we're starting fresh
                        self.queue_manager.clear_queue_state()
                else:
                    # No music playing and no active queue - start fresh
                    print(f"Starting fresh playback with '{file_name}'")
                    self.launch_music_player(file_path, file_name)
                    # Clear any stale queue state
                    self.queue_manager.clear_queue_state()
            else:
                # Non-macOS platforms - use regular launch behavior
                self.launch_music_player(file_path, file_name)
            
        except Exception as e:
            print(f"Error playing song {item_id}: {e}")
            import traceback
            traceback.print_exc()

    def on_play_all(self):
        """Handle Play All button - play all songs in current view sequentially."""
        try:
            # Get current songs list
            current_songs = []
            
            if self.navigation_state["is_drilled_down"]:
                # Use songs from drilled-down category
                current_songs = self.navigation_state["category_songs"]
            else:
                # Get songs from current filter
                current_filter = getattr(self, 'filter_var', None)
                if current_filter:
                    filter_type = current_filter.get()
                    if filter_type in ["Music", "Music: Artist", "Music: Album", "Music: Genre", "Music: Mood", "Music: Year"]:
                        current_songs = self.db.search_filtered("", filter_type)
                    
            if not current_songs:
                print("No songs to play")
                return
                
            # Create playlist of file paths
            playlist = []
            for song_row in current_songs:
                file_path = self.get_music_file_path(song_row)
                if file_path:
                    playlist.append((file_path, song_row["file_name"]))
            
            if not playlist:
                print("No playable songs found")
                return
            
            # Check if there's an existing queue and prompt user
            if hasattr(self, 'queue_manager') and self.queue_manager.has_active_queue():
                from tkinter import messagebox
                user_choice = messagebox.askyesnocancel(
                    "Queue Action",
                    f"There are {len(self.queue_manager.local_queue)} songs currently in the queue.\n\n"
                    f"Would you like to:\n"
                    f"• Yes: Replace the current queue with {len(playlist)} new songs\n"
                    f"• No: Add {len(playlist)} songs to the end of the current queue\n"
                    f"• Cancel: Keep the current queue unchanged",
                    icon="question"
                )
                
                if user_choice is None:  # Cancel
                    return
                elif user_choice is False:  # No - Append to queue
                    self.append_to_music_queue(playlist)
                    return
                # If Yes (True), continue with normal playlist launch (replace queue)
                
            # Launch playlist (replace queue or start new)
            self.launch_music_playlist(playlist)
            
        except Exception as e:
            print(f"Error playing all songs: {e}")
            import traceback
            traceback.print_exc()

    def append_to_music_queue(self, new_playlist):
        """Append songs to the existing music queue."""
        try:
            if not hasattr(self, 'queue_manager') or not self.queue_manager:
                print("No queue manager available, falling back to regular playlist")
                self.launch_music_playlist(new_playlist)
                return
            
            # Get current queue
            current_queue = self.queue_manager.local_queue.copy()
            
            # Append new songs to existing queue
            combined_queue = current_queue + new_playlist
            
            print(f"Appending {len(new_playlist)} songs to existing queue of {len(current_queue)} songs")
            print(f"Total queue will have {len(combined_queue)} songs")
            
            # Update the queue manager's local queue
            self.queue_manager.local_queue = combined_queue
            
            # Recreate the playlist with the combined queue
            success = self._recreate_playlist_with_queue(combined_queue)
            
            if success:
                self.queue_manager.last_queue_time = time.time()
                print(f"✓ Queue updated with {len(combined_queue)} songs total")
            else:
                print("✗ Failed to append to queue, falling back to regular playlist")
                self.launch_music_playlist(new_playlist)
                
        except Exception as e:
            print(f"Error appending to music queue: {e}")
            import traceback
            traceback.print_exc()
            # Fallback to regular playlist
            self.launch_music_playlist(new_playlist)

    def get_music_file_path(self, row):
        """Get the full file path for a music record."""
        try:
            if row["file_path"]:
                from pathlib import Path
                file_path = Path(row["file_path"])
                if file_path.exists():
                    return str(file_path)
                    
            # Fallback: try photos_export directory
            from pathlib import Path
            fallback_path = Path("photos_export") / row["file_name"]
            if fallback_path.exists():
                return str(fallback_path)
                
            return None
            
        except Exception as e:
            print(f"Error getting file path for {row['file_name']}: {e}")
            return None

    def launch_music_player(self, file_path, song_name):
        """Launch system music player for a single song."""
        try:
            import subprocess
            import sys
            
            print(f"Playing: {song_name}")
            print(f"File: {file_path}")
            
            # Update queue manager state when launching single song
            if hasattr(self, 'queue_manager') and self.queue_manager:
                single_song_playlist = [(file_path, song_name)]
                self.queue_manager.local_queue = single_song_playlist
                self.queue_manager.last_queue_time = time.time()
                print(f"Updated queue manager with 1 song")
            
            if sys.platform == "darwin":  # macOS - Use AppleScript for better integration
                self._play_single_song_applescript(file_path, song_name)
            elif sys.platform == "win32":  # Windows
                subprocess.Popen(["start", file_path], shell=True)
            else:  # Linux
                subprocess.Popen(["xdg-open", file_path])
                
        except Exception as e:
            print(f"Error launching music player: {e}")

    def _play_single_song_applescript(self, file_path, song_name):
        """Play a single song using AppleScript on macOS."""
        try:
            import subprocess
            
            # Use the simpler approach: open the file directly with Music app
            result = subprocess.run(['open', '-a', 'Music', file_path],
                                 capture_output=True, text=True, timeout=15)
            
            if result.returncode == 0:
                print(f"✓ Playing '{song_name}' in Music app")
            else:
                print(f"Music app open error: {result.stderr}")
                # Fallback to simple open command
                subprocess.Popen(["open", file_path])
                    
        except Exception as e:
            print(f"AppleScript single song error: {e}")
            # Fallback to opening the file
            subprocess.Popen(["open", file_path])

    def _check_music_playing_applescript(self):
        """Check if Music app is currently playing and has content."""
        try:
            import subprocess
            
            script = '''
            tell application "Music"
                try
                    set playerState to player state
                    set currentTrack to current track
                    if playerState is playing or playerState is paused then
                        return "playing"
                    else
                        return "stopped"
                    end if
                on error
                    return "stopped"
                end try
            end tell
            '''
            
            result = subprocess.run(['osascript', '-e', script],
                                 capture_output=True, text=True, timeout=10)
            
            if result.returncode == 0:
                state = result.stdout.strip()
                return state == "playing"
            else:
                print(f"Music state check error: {result.stderr}")
                return False
                
        except Exception as e:
            print(f"Error checking Music state: {e}")
            return False


    def launch_music_playlist(self, playlist):
        """Launch system music player with a playlist of songs using AppleScript queue."""
        try:
            import subprocess
            import sys
            
            print(f"Playing playlist of {len(playlist)} songs:")
            for i, (file_path, song_name) in enumerate(playlist[:5]):  # Show first 5
                print(f"  {i+1}. {song_name}")
            if len(playlist) > 5:
                print(f"  ... and {len(playlist) - 5} more")
            
            if not playlist:
                return
                
            # Update queue manager state when launching playlist
            if hasattr(self, 'queue_manager') and self.queue_manager:
                self.queue_manager.local_queue = playlist.copy()
                self.queue_manager.last_queue_time = time.time()
                print(f"Updated queue manager with {len(playlist)} songs")
                
            if sys.platform == "darwin":  # macOS - Use AppleScript for proper queuing
                self._add_songs_to_music_queue_applescript(playlist)
            elif sys.platform == "win32":  # Windows
                first_file = playlist[0][0]
                subprocess.Popen(["start", first_file], shell=True)
            else:  # Linux
                first_file = playlist[0][0]
                subprocess.Popen(["xdg-open", first_file])
                    
        except Exception as e:
            print(f"Error launching music playlist: {e}")

    def _add_songs_to_music_queue_applescript(self, playlist):
        """Create temporary playlist and play it sequentially using AppleScript."""
        try:
            import subprocess
            import tempfile
            import os
            import datetime
            
            # Create unique playlist name
            timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
            playlist_name = f"MediaVault_Temp_{timestamp}"
            
            print(f"Creating temporary playlist: {playlist_name}")
            
            # Create AppleScript to create playlist and add songs
            applescript = f'''
tell application "Music"
    activate
    
    -- Create temporary playlist
    set tempPlaylist to make new playlist with properties {{name:"{playlist_name}"}}
    
    -- Add songs to the playlist
'''
            
            # Add each song to the playlist
            for file_path, song_name in playlist:
                # Escape the file path for AppleScript
                escaped_path = file_path.replace("\\", "\\\\").replace('"', '\\"')
                applescript += f'''
    try
        set theTrack to add POSIX file "{escaped_path}"
        if theTrack is not missing value then
            duplicate theTrack to tempPlaylist
        end if
    on error errMsg
        -- Skip files that can't be added
    end try
'''
            
            applescript += f'''
    
    -- Play the playlist
    try
        play tempPlaylist
    on error errMsg
        -- If playlist play fails, try first track
        try
            set firstTrack to track 1 of tempPlaylist
            play firstTrack
        end try
    end try
    
end tell
'''
            
            # Write AppleScript to temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.scpt', delete=False) as f:
                f.write(applescript)
                script_path = f.name
            
            try:
                # Execute the AppleScript
                result = subprocess.run(['osascript', script_path], 
                                     capture_output=True, text=True, timeout=60)
                
                if result.returncode == 0:
                    print(f"✓ Temporary playlist '{playlist_name}' created and playing")
                    print(f"   Playlist will auto-cleanup after 24 hours, or delete manually in Music app")
                    
                    # Schedule cleanup after 24 hours to prevent long-term accumulation
                    # Users can manually delete earlier if desired
                    self._schedule_playlist_cleanup(playlist_name)
                else:
                    print(f"AppleScript playlist error: {result.stderr}")
                    # Fallback to opening files
                    file_paths = [item[0] for item in playlist]
                    subprocess.Popen(["open", "-a", "Music"] + file_paths)
                    
            finally:
                # Clean up script file
                try:
                    os.unlink(script_path)
                except Exception:
                    pass
                    
        except Exception as e:
            print(f"AppleScript playlist error: {e}")
            # Fallback to opening all files
            file_paths = [item[0] for item in playlist]
            subprocess.Popen(["open"] + file_paths)

    def _schedule_playlist_cleanup(self, playlist_name):
        """Schedule cleanup of temporary playlist after 24 hours."""
        import threading
        import time
        
        def cleanup():
            try:
                # Wait 24 hours before cleanup - allows for very long playlists
                # Users can manually delete playlists in Music app if desired
                time.sleep(24 * 60 * 60)  # 24 hours = 86,400 seconds
                self._cleanup_temp_playlist(playlist_name)
            except Exception as e:
                print(f"Cleanup error: {e}")
        
        # Run cleanup in background thread
        threading.Thread(target=cleanup, daemon=True).start()
    
    def _cleanup_temp_playlist(self, playlist_name):
        """Remove temporary playlist after use."""
        try:
            import subprocess
            import tempfile
            import os
            
            applescript = f'''
tell application "Music"
    try
        delete playlist "{playlist_name}"
    on error errMsg
        -- Playlist might already be deleted or not exist
    end try
end tell
'''
            
            with tempfile.NamedTemporaryFile(mode='w', suffix='.scpt', delete=False) as f:
                f.write(applescript)
                script_path = f.name
            
            try:
                result = subprocess.run(['osascript', script_path], 
                                     capture_output=True, text=True, timeout=15)
                if result.returncode == 0:
                    print(f"✓ Cleaned up temporary playlist: {playlist_name}")
                    
            finally:
                try:
                    os.unlink(script_path)
                except Exception:
                    pass
                    
        except Exception as e:
            print(f"Playlist cleanup error: {e}")

    def cleanup_all_temp_playlists(self):
        """Manually cleanup all MediaVault temporary playlists."""
        try:
            import subprocess
            import tempfile
            import os
            
            applescript = '''
tell application "Music"
    try
        set tempPlaylists to every playlist whose name starts with "MediaVault_Temp_"
        repeat with tempPlaylist in tempPlaylists
            delete tempPlaylist
        end repeat
        return (count of tempPlaylists) as string
    on error errMsg
        return "0"
    end try
end tell
'''
            
            with tempfile.NamedTemporaryFile(mode='w', suffix='.scpt', delete=False) as f:
                f.write(applescript)
                script_path = f.name
            
            try:
                result = subprocess.run(['osascript', script_path], 
                                     capture_output=True, text=True, timeout=15)
                if result.returncode == 0:
                    count = result.stdout.strip()
                    print(f"✓ Cleaned up {count} temporary playlists")
                    return int(count) if count.isdigit() else 0
                    
            finally:
                try:
                    os.unlink(script_path)
                except Exception:
                    pass
                    
        except Exception as e:
            print(f"Manual cleanup error: {e}")
            return 0

    def _recreate_playlist_with_queue(self, queue_songs):
        """Recreate the temporary playlist with a new queue of songs."""
        try:
            import subprocess
            import tempfile
            import os
            import time
            
            if not queue_songs:
                print("No songs in queue to recreate")
                return False
            
            # Delete existing temp playlist if it exists
            if hasattr(self.queue_manager, 'current_temp_playlist') and self.queue_manager.current_temp_playlist:
                self._cleanup_temp_playlist(self.queue_manager.current_temp_playlist)
            
            # Create new unique playlist name
            timestamp = int(time.time())
            playlist_name = f"MediaVault_Queue_{timestamp}"
            
            print(f"Creating queue playlist: {playlist_name} with {len(queue_songs)} songs")
            
            # Create AppleScript to create playlist and add songs
            script_lines = [
                'tell application "Music"',
                '    try',
                f'        set tempPlaylist to make new playlist with properties {{name:"{playlist_name}"}}',
                '        '
            ]
            
            # Add each song to the playlist
            for file_path, song_name in queue_songs:
                # Escape quotes in file path
                escaped_path = file_path.replace('"', '\\"')
                script_lines.extend([
                    f'        try',
                    f'            set theTrack to add (POSIX file "{escaped_path}") to tempPlaylist',
                    f'        on error errMsg',
                    f'            -- Skip files that cannot be added',
                    f'        end try'
                ])
            
            script_lines.extend([
                '        ',
                '        -- Play the playlist',
                '        try',
                f'            play playlist "{playlist_name}"',
                '        on error',
                '            -- If playlist play fails, try first track',
                '            try',
                '                play (first track of tempPlaylist)',
                '            on error',
                '                -- Final fallback',
                '            end try',
                '        end try',
                '        ',
                '        return "success"',
                '    on error errMsg',
                '        return "error: " & errMsg',
                '    end try',
                'end tell'
            ])
            
            script_content = '\n'.join(script_lines)
            
            # Write script to temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.scpt', delete=False) as f:
                f.write(script_content)
                script_path = f.name
            
            try:
                # Execute the script
                result = subprocess.run(['osascript', script_path],
                                     capture_output=True, text=True, timeout=30)
                
                if result.returncode == 0 and "success" in result.stdout:
                    print(f"✓ Queue playlist '{playlist_name}' created and playing")
                    
                    # Update queue manager state
                    self.queue_manager.current_temp_playlist = playlist_name
                    
                    # Schedule cleanup
                    self._schedule_playlist_cleanup(playlist_name)
                    return True
                else:
                    print(f"Queue playlist creation error: {result.stderr}")
                    return False
                    
            finally:
                try:
                    os.unlink(script_path)
                except Exception:
                    pass
                    
        except Exception as e:
            print(f"Queue recreation error: {e}")
            return False

    def show_play_all_button(self):
        """Show the Play All button when appropriate."""
        current_filter = getattr(self, 'filter_var', None)
        if current_filter:
            filter_type = current_filter.get()
            if filter_type in ["Music", "Music: Artist", "Music: Album", "Music: Genre", "Music: Mood", "Music: Year"] or self.navigation_state["is_drilled_down"]:
                self.play_all_button.pack(side="left", padx=(5, 0))
            else:
                self.play_all_button.pack_forget()

    def hide_play_all_button(self):
        """Hide the Play All button."""
        self.play_all_button.pack_forget()

    # --------------------------------------------------------------------
    # Record handling
    # --------------------------------------------------------------------
    def load_record(self, file_name: str):
        import sys
        print(f"DEBUG: load_record called with: {file_name}", file=sys.stderr)
        # First completely cleanup any media players
        self.stop_video()
        if self.video_player:
            self.video_player.destroy()
            self.video_player = None
        if self.video_frame:
            self.video_frame.destroy()
            self.video_frame = None
        
        # Clean up any image resources
        if hasattr(self, 'current_img') and self.current_img:
            try:
                self.current_img.close()
            except Exception:
                pass
            self.current_img = None
        
        # Clear video controls
        self.video_controls.pack_forget()
        for widget in self.video_controls.winfo_children():
            widget.destroy()
        
        # Hide image preview if it exists
        if hasattr(self, 'image_frame') and self.image_frame:
            self.image_frame.pack_forget()
        
        row = self.db.fetch_one(file_name)
        if not row:
            print(f"DEBUG: No row found for {file_name}", file=sys.stderr)
            return
        self.current_file = row["file_name"]
        print(f"DEBUG: Row found, proceeding with media detection", file=sys.stderr)

        # Determine file path and extension first
        db_file_path = row["file_path"] if row["file_path"] else ""
        if db_file_path:
            file_path = Path(db_file_path)
        else:
            file_path = PHOTOS_DIR / row["file_name"]
        
        # Use the database file_ext field instead of path suffix for more reliable detection
        file_ext = row["file_ext"] if row["file_ext"] else file_path.suffix.lower()
        if not file_ext.startswith('.') and file_ext:
            file_ext = '.' + file_ext  # Add dot if missing
        
        is_music = file_ext.lstrip('.').lower() in [ext.lstrip('.').lower() for ext in MUSIC_EXTENSIONS]
        print(f"DEBUG: file_ext='{file_ext}', is_music={is_music}", file=sys.stderr)
        
        # Display read-only information - different fields for music vs other media
        self.fn_lbl.config(text=row["file_name"])
        self.id_lbl.config(text=row["id"])
        
        if is_music:
            print(f"DEBUG: Processing music file", file=sys.stderr)
            # Music-specific information display - show date_original like other media types
            self.date_lbl.config(text=row["date_original"] if row["date_original"] else "Unknown")
            
            rating_key = row["rating_key"] if row["rating_key"] else "N/A"
            self.loc_lbl.config(text=f"Rating Key: {rating_key}")
            
            print(f"DEBUG: About to call show_music_info_fields", file=sys.stderr)
            # Show music-specific fields
            self.show_music_info_fields(row)
            print(f"DEBUG: show_music_info_fields completed", file=sys.stderr)
            
        else:
            # Standard display for photos/videos
            self.date_lbl.config(text=row["date_original"] or "Unknown")
            
            # Location coordinates
            if row["latitude"] is not None and row["longitude"] is not None:
                self.loc_lbl.config(text=f"{row['latitude']}, {row['longitude']}")
            else:
                self.loc_lbl.config(text="Unknown")
                
            # Hide music-specific fields
            self.hide_music_info_fields()

        # Debug: Check if file exists
        if not file_path.exists():
            print(f"Warning: Media file not found: {file_path}")
        
        # Determine media type from file extension 
        if is_music:
            media_type = "music"
        elif file_ext.lstrip('.') in [ext.lstrip('.') for ext in VIDEO_EXTENSIONS]:
            media_type = "video"
        else:
            media_type = "photo"
        
        print(f"DEBUG: File extension: {file_ext}, File path: {file_path}, Media type: {media_type}", file=sys.stderr)
        
        # Set up preview based on determined media type
        print(f"DEBUG: About to set up preview for media_type: {media_type}", file=sys.stderr)
        if media_type == "music":
            print(f"DEBUG: Setting up MUSIC preview for: {file_path.name}")
            try:
                self.setup_music_preview(file_path, row)
                print(f"DEBUG: setup_music_preview completed successfully")
            except Exception as e:
                print(f"DEBUG: ERROR in setup_music_preview: {e}")
                import traceback
                traceback.print_exc()
        elif media_type == "video":
            print(f"DEBUG: Setting up VIDEO preview for: {file_path.name}")
            self.video_rotation = 0 # Reset rotation for new video
            # Set up embedded video player with full controls
            self.setup_embedded_video_player(file_path)
        else:
            print(f"DEBUG: Setting up PHOTO preview for: {file_path.name}")
            self.current_img_rotation = 0 # Reset rotation for new image
            self.setup_image_preview(file_path)

        # Create appropriate form based on media type
        self.create_form_for_media_type(media_type)
        
        # Populate form fields based on media type
        if media_type == "music":
            self.load_music_fields(row)
        else:  # photo or video
            self.load_visual_fields(row)

    def show_music_info_fields(self, row):
        """Show and populate music-specific fields in the file information frame."""
        row_num = 4  # Start after the basic info fields
        
        # Artist
        self.music_info_labels["artist"].grid(row=row_num, column=0, sticky="w", pady=2)
        artist = row["artist"] if row["artist"] and row["artist"] != "None" else "Unknown Artist"
        self.music_info_values["artist"].config(text=artist)
        self.music_info_values["artist"].grid(row=row_num, column=1, sticky="w", pady=2)
        row_num += 1
        
        # Album
        self.music_info_labels["album"].grid(row=row_num, column=0, sticky="w", pady=2)
        album = row["album"] if row["album"] and row["album"] != "None" else "Unknown Album"
        self.music_info_values["album"].config(text=album)
        self.music_info_values["album"].grid(row=row_num, column=1, sticky="w", pady=2)
        row_num += 1
        
        # Date Original
        self.music_info_labels["date_orig"].grid(row=row_num, column=0, sticky="w", pady=2)
        date_orig = row["date_original"] if row["date_original"] else "Unknown"
        self.music_info_values["date_orig"].config(text=date_orig)
        self.music_info_values["date_orig"].grid(row=row_num, column=1, sticky="w", pady=2)
        row_num += 1
        
        # File Path
        self.music_info_labels["filepath"].grid(row=row_num, column=0, sticky="w", pady=2)
        file_path_str = row["file_path"] if row["file_path"] else "N/A"
        # Truncate very long paths
        if len(file_path_str) > 50:
            file_path_str = "..." + file_path_str[-47:]
        self.music_info_values["filepath"].config(text=file_path_str)
        self.music_info_values["filepath"].grid(row=row_num, column=1, sticky="w", pady=2)
        row_num += 1
        
        # Play button
        self.play_button_frame.grid(row=row_num, column=0, columnspan=2, pady=5, sticky="w")
        
        # Store current file path for play button
        self.current_music_file_path = row["file_path"] if row["file_path"] else None

    def hide_music_info_fields(self):
        """Hide music-specific fields from the file information frame."""
        # Hide all music-specific labels and values
        for label in self.music_info_labels.values():
            label.grid_remove()
        for value in self.music_info_values.values():
            value.grid_remove()
        self.play_button_frame.grid_remove()
        
        # Clear current music file path
        self.current_music_file_path = None

    def play_current_music_file(self):
        """Play the currently selected music file using the system's default player."""
        if hasattr(self, 'current_music_file_path') and self.current_music_file_path:
            file_path = Path(self.current_music_file_path)
            if file_path.exists():
                try:
                    # Use the existing open_with_default_app function
                    process = open_with_default_app(str(file_path), self)
                    if process:
                        self.current_video_process = process  # Track for cleanup
                    print(f"Playing music file: {file_path.name}")
                except Exception as e:
                    messagebox.showerror("Error", f"Could not play music file: {e}")
            else:
                messagebox.showerror("Error", "Music file not found")
        else:
            messagebox.showerror("Error", "No music file selected")

    def setup_image_preview(self, img_path: Path):
        """Set up the image preview."""
        # Clean up video player components
        self.stop_video()
        if self.video_player:
            self.video_player.destroy()
            self.video_player = None
        if self.video_frame:
            self.video_frame.destroy()
            self.video_frame = None
        
        # Clear video controls and click handlers
        self.video_controls.pack_forget()
        for widget in self.video_controls.winfo_children():
            widget.destroy()
        self.preview_lbl.unbind("<Button-1>")
        self.preview_lbl.configure(cursor="")
        
        # Clear music controls if they exist
        if hasattr(self, 'music_controls'):
            self.music_controls.pack_forget()
            for widget in self.music_controls.winfo_children():
                widget.destroy()
        
        # Hide existing image frame if it exists
        if hasattr(self, 'image_frame') and self.image_frame:
            self.image_frame.pack_forget()
        
        # Reset rotation
        self.current_img_rotation = 0
        self.current_img = None
        self.current_img_path = img_path
        
        # Create image preview frame if it doesn't exist
        if not hasattr(self, 'image_frame') or not self.image_frame:
            self.image_frame = ttk.Frame(self.preview_frame)
            
            # Image preview label - use the existing one but reparent it
            if hasattr(self, 'preview_lbl') and self.preview_lbl:
                self.preview_lbl.destroy()
            self.preview_lbl = ttk.Label(self.image_frame)
            self.preview_lbl.pack(anchor="center", pady=10)
            
            # Image controls
            self.image_controls = ttk.Frame(self.image_frame)
            self.image_controls.pack(fill="x", pady=5)
            
            # Rotation buttons  (replace only the command= parts)
            ttk.Button(self.image_controls, text="Rotate Left",
                      command=lambda: (self.rotate_image(-90))
            ).pack(side="left", padx=5)

            ttk.Button(self.image_controls, text="Rotate Right",
                      command=lambda: (self.rotate_image(90))
            ).pack(side="left", padx=5)

            ttk.Button(self.image_controls, text="Save Rotation",
                      command=lambda: (self.save_rotated_image())
            ).pack(side="left", padx=5)
            
            # Image info
            info_label = ttk.Label(self.image_controls, text=f"Image: {img_path.name}")
            info_label.pack(side="right", padx=5)
        
        # Always pack the image frame
        self.image_frame.pack(fill="both", expand=True)
        
        # Load and display the image
        if img_path.is_file() and img_path.suffix.lower() in {".jpg", ".jpeg", ".png", ".gif"}:
            try:
                self.current_img = Image.open(img_path)
                self.display_image()
            except Exception as e:
                print(f"PIL error: {e}")
                self.preview_lbl.configure(image=self.default_img)
        else:
            self.preview_lbl.configure(image=self.default_img)
    
    def display_image(self):
        """Display the current image with rotation applied."""
        if not self.current_img:
            return
            
        try:
            # Apply rotation (negative angle for clockwise display matching user expectation)
            rotated_img = self.current_img.rotate(-self.current_img_rotation, expand=True)
            
            # Resize for display
            rotated_img.thumbnail(IMAGE_MAX, Image.LANCZOS)
            
            # Convert to PhotoImage
            self.tk_img = ImageTk.PhotoImage(rotated_img)
            self.preview_lbl.configure(image=self.tk_img)
            
            # Clean up the rotated image since we've converted it
            rotated_img.close()
        except Exception as e:
            print(f"Error displaying image: {e}")
            if hasattr(self, 'default_img') and self.default_img:
                self.preview_lbl.configure(image=self.default_img)
        
    def rotate_image(self, angle):
        """Rotate the image by the specified angle."""
        if not self.current_img:
            return
            
        # Update rotation angle
        self.current_img_rotation = (self.current_img_rotation + angle) % 360
        
        # Redisplay the image
        self.display_image()
    
    
    def setup_video_player(self, video_path: Path):
        """Set up the embedded video player with sound and launch button."""
        # First clean up any existing video or image components
        self.stop_video()
        self.preview_lbl.pack_forget()
        
        if self.video_player:
            self.video_player.destroy()
            self.video_player = None
        
        if self.video_frame:
            self.video_frame.destroy()
            self.video_frame = None
        
        # Clear video controls
        self.video_controls.pack_forget()
        for widget in self.video_controls.winfo_children():
            widget.destroy()
            
        if not video_path.exists():
            print(f"Video file not found: {video_path}")
            self.preview_lbl.configure(image=self.default_img)
            self.preview_lbl.pack(anchor="center")
            return
            
        self.current_video_path = video_path
        
        # Try TkVideoPlayer first (has built-in audio support)
        if has_tkvideoplayer:
            try:
                self.video_frame = ttk.Frame(self.preview_frame, width=VIDEO_MAX[0], height=VIDEO_MAX[1])
                self.video_frame.pack(anchor="center")
                
                self.video_player = TkVideoPlayer(self.video_frame, scaled=True)
                self.video_player.load(str(video_path))
                self.video_player.pack(expand=True, fill="both")
                
                # Video controls
                self.video_controls = ttk.Frame(self.preview_frame)
                self.video_controls.pack(fill="x", pady=5)
                
                ttk.Button(self.video_controls, text="Play", command=self.play_video).pack(side="left", padx=5)
                ttk.Button(self.video_controls, text="Pause", command=self.pause_video).pack(side="left", padx=5)
                ttk.Button(self.video_controls, text="Stop", command=self.stop_video).pack(side="left", padx=5)
                
                # Launch external player button
                ttk.Button(self.video_controls, text="Launch Video Player", 
                          command=lambda: self.launch_external_player(video_path)).pack(side="right", padx=5)
                
                print(f"Loaded video with TkVideoPlayer (with sound): {video_path.name}")
                
                # Auto-play the video
                self.after(100, self.play_video)  # Small delay to ensure player is ready
                return
                
            except Exception as e:
                print(f"TkVideoPlayer failed: {e}")
        
        # Fall back to OpenCV + VLC audio combination
        if has_cv2:
            try:
                self.video_frame = ttk.Frame(self.preview_frame, width=VIDEO_MAX[0], height=VIDEO_MAX[1])
                self.video_frame.pack(anchor="center")
                
                # Create a canvas for displaying frames
                self.video_canvas = tk.Canvas(self.video_frame, width=VIDEO_MAX[0], height=VIDEO_MAX[1], bg="black")
                self.video_canvas.pack()
                
                self.display_video_thumbnail(video_path)
                
                # Setup VLC for audio playback
                self.setup_video_audio(video_path)
                
                # Video controls
                self.video_controls = ttk.Frame(self.preview_frame)
                self.video_controls.pack(fill="x", pady=5)
                
                ttk.Button(self.video_controls, text="Play", command=self.play_video).pack(side="left", padx=5)
                ttk.Button(self.video_controls, text="Stop", command=self.stop_video).pack(side="left", padx=5)
                
                # Volume control
                tk.Label(self.video_controls, text="Vol:").pack(side="left", padx=(10,2))
                self.volume_scale = tk.Scale(self.video_controls, from_=0, to=100, orient='horizontal',
                                            command=self.set_volume, length=100)
                self.volume_scale.set(80)
                self.volume_scale.pack(side="left", padx=2)
                
                # Launch external player button
                ttk.Button(self.video_controls, text="Launch Video Player", 
                          command=lambda: self.launch_external_player(video_path)).pack(side="right", padx=5)
                
                print(f"Loaded video with OpenCV + VLC audio: {video_path.name}")
                
                # Auto-play the video
                self.after(100, self.play_video)  # Small delay to ensure player is ready
                return
                
            except Exception as e:
                print(f"OpenCV + VLC setup failed: {e}")
        
        # Final fallback - just show launch button
        self.setup_system_player(video_path)

    def setup_video_message(self, video_path: Path):
        """Show a simple message that the video was launched in default player."""
        # Clean up any existing video components
        self.stop_video()
        if self.video_player:
            self.video_player.destroy()
            self.video_player = None
        if self.video_frame:
            self.video_frame.destroy()
            self.video_frame = None
        
        # Clear video controls
        self.video_controls.pack_forget()
        for widget in self.video_controls.winfo_children():
            widget.destroy()
        
        # Hide existing image frame if it exists
        if hasattr(self, 'image_frame') and self.image_frame:
            self.image_frame.pack_forget()
        
        # Show the main preview label with a message
        self.preview_lbl.pack(anchor="center")
        
        # Create a simple message image
        try:
            # Create a simple text-based image
            from PIL import Image, ImageDraw, ImageFont
            img = Image.new('RGB', (400, 200), color='lightgray')
            draw = ImageDraw.Draw(img)
            
            # Try to use a default font, fall back to basic if not available
            try:
                font = ImageFont.truetype("Arial.ttf", 16)
            except:
                font = ImageFont.load_default()
            
            text = f"Video opened in default player:\n{video_path.name}"
            draw.text((20, 80), text, fill='black', font=font)
            
            # Convert to PhotoImage
            self.tk_img = ImageTk.PhotoImage(img)
            self.preview_lbl.configure(image=self.tk_img, text="")
            
        except Exception as e:
            # Fallback to text-only
            self.preview_lbl.configure(image=self.default_img, 
                                     text=f"Video opened in default player:\n{video_path.name}")

    def setup_video_preview(self, video_path: Path):
        """Set up video preview with thumbnail and click-to-play functionality."""
        # Clean up any existing video components
        self.stop_video()
        if self.video_player:
            self.video_player.destroy()
            self.video_player = None
        if self.video_frame:
            self.video_frame.destroy()
            self.video_frame = None
        
        # Clear video controls
        self.video_controls.pack_forget()
        for widget in self.video_controls.winfo_children():
            widget.destroy()
        
        # Store current video path
        self.current_video_path = video_path
        
        # Show preview label (will be populated with thumbnail or fallback)
        self.preview_lbl.pack(anchor="center")
        
        # Try to create thumbnail from first good frame
        thumbnail_created = False
        if has_cv2 and video_path.exists():
            try:
                cap = cv2.VideoCapture(str(video_path))
                frame = None
                frame_found = False
                
                # Try to get first non-blank frame (up to first 30 frames)
                for frame_num in range(30):
                    cap.set(cv2.CAP_PROP_POS_FRAMES, frame_num)
                    ret, temp_frame = cap.read()
                    
                    if ret and temp_frame is not None:
                        # Check if frame is not completely black/blank
                        gray_frame = cv2.cvtColor(temp_frame, cv2.COLOR_BGR2GRAY)
                        mean_brightness = cv2.mean(gray_frame)[0]
                        
                        # Frame has some content (not completely black)
                        if mean_brightness > 15:
                            frame = temp_frame
                            frame_found = True
                            print(f"Found good frame at position {frame_num} (brightness: {mean_brightness:.1f})")
                            break
                
                cap.release()
                
                if frame_found and frame is not None:
                    # Convert BGR to RGB
                    frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                    
                    # Apply rotation if needed
                    if self.video_rotation != 0:
                        if self.video_rotation == 90:
                            frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_90_CLOCKWISE)
                        elif self.video_rotation == 180:
                            frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_180)
                        elif self.video_rotation == 270:
                            frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_90_COUNTERCLOCKWISE)
                    
                    # Resize to fit preview area
                    h, w = frame_rgb.shape[:2]
                    aspect_ratio = w / h
                    max_w, max_h = IMAGE_MAX
                    
                    if aspect_ratio > max_w / max_h:
                        new_w = max_w
                        new_h = int(max_w / aspect_ratio)
                    else:
                        new_h = max_h
                        new_w = int(max_h * aspect_ratio)
                    
                    # Convert to PIL Image and resize
                    pil_image = Image.fromarray(frame_rgb)
                    pil_image = pil_image.resize((new_w, new_h), Image.Resampling.LANCZOS)
                    
                    # Convert to PhotoImage
                    self.tk_img = ImageTk.PhotoImage(pil_image)
                    
                    # Configure label with thumbnail and add click handler
                    self.preview_lbl.configure(image=self.tk_img, text="")
                    self.preview_lbl.bind("<Button-1>", lambda e: self.launch_external_player(video_path))
                    self.preview_lbl.configure(cursor="hand2")  # Show it's clickable
                    
                    thumbnail_created = True
                    print(f"Video thumbnail created for: {video_path.name}")
                    
            except Exception as e:
                print(f"Error creating video thumbnail: {e}")
        
        # Fallback if no thumbnail created
        if not thumbnail_created:
            # Create a simple video preview image
            try:
                from PIL import ImageDraw, ImageFont
                img = Image.new('RGB', IMAGE_MAX, color='lightgray')
                draw = ImageDraw.Draw(img)
                
                try:
                    font = ImageFont.truetype("Arial.ttf", 20)
                except:
                    font = ImageFont.load_default()
                
                text_lines = [
                    "🎬 VIDEO",
                    f"{video_path.name}",
                    "",
                    "Click to play"
                ]
                
                y_offset = 50
                for line in text_lines:
                    bbox = draw.textbbox((0, 0), line, font=font)
                    text_width = bbox[2] - bbox[0]
                    x = (IMAGE_MAX[0] - text_width) // 2
                    draw.text((x, y_offset), line, fill='black', font=font)
                    y_offset += 35
                
                # Convert to PhotoImage
                self.tk_img = ImageTk.PhotoImage(img)
                self.preview_lbl.configure(image=self.tk_img, text="")
                
            except Exception as e:
                print(f"Error creating video preview image: {e}")
                # Final fallback to text only
                self.preview_lbl.configure(image=self.default_img, 
                                         text=f"🎬 VIDEO\n{video_path.name}\n\nClick to play")
            
            # Add click handler for fallback mode
            self.preview_lbl.bind("<Button-1>", lambda e: self.launch_external_player(video_path))
            self.preview_lbl.configure(cursor="hand2")
        
        # Always add a play button below the preview
        self.video_controls = ttk.Frame(self.preview_frame)
        self.video_controls.pack(fill="x", pady=5)
        
        play_button = ttk.Button(
            self.video_controls, 
            text="▶️ Play Video", 
            command=lambda: self.launch_external_player(video_path)
        )
        play_button.pack(side="left", padx=5)
        
        # Add video info label
        info_label = ttk.Label(
            self.video_controls, 
            text=f"Video: {video_path.name}"
        )
        info_label.pack(side="left", padx=10)

    def setup_embedded_video_player(self, video_path: Path):
        """Set up simple embedded video player with VLC for audio+video."""
        # Clean up any existing video components
        self.stop_video()
        if self.video_player:
            self.video_player.destroy()
            self.video_player = None
        if self.video_frame:
            self.video_frame.destroy()
            self.video_frame = None
        
        # Clear existing video controls
        self.video_controls.pack_forget()
        for widget in self.video_controls.winfo_children():
            widget.destroy()
        
        # Clear music controls if they exist
        if hasattr(self, 'music_controls'):
            self.music_controls.pack_forget()
            for widget in self.music_controls.winfo_children():
                widget.destroy()
        
        # Clear image controls if they exist  
        if hasattr(self, 'image_frame') and self.image_frame:
            self.image_frame.pack_forget()
            if hasattr(self, 'image_controls'):
                for widget in self.image_controls.winfo_children():
                    widget.destroy()
        
        # Store current video path
        self.current_video_path = video_path
        self.video_playing = False
        
        if not video_path.exists():
            self.setup_video_preview(video_path)
            return
        
        try:
            # Show thumbnail first
            if has_cv2:
                self.display_video_thumbnail_simple(video_path)
            else:
                # Fallback to text
                self.preview_lbl.configure(image=self.default_img, 
                                         text=f"🎬 VIDEO\n{video_path.name}")
                self.preview_lbl.pack(anchor="center")
            
            # Simple control panel
            self.video_controls = ttk.Frame(self.preview_frame)
            self.video_controls.pack(fill="x", pady=5)
            
            # Simple controls
            ttk.Button(self.video_controls, text="▶️ Play Video", command=lambda: self.play_video_vlc(video_path)).pack(side="left", padx=5)
            ttk.Button(self.video_controls, text="🎬 Open in Player", command=lambda: self.launch_external_player(video_path)).pack(side="left", padx=5)
            
            # Video info
            info_label = ttk.Label(self.video_controls, text=f"Video: {video_path.name}")
            info_label.pack(side="right", padx=5)
            
            print(f"Simple video player initialized for: {video_path.name}")
            
        except Exception as e:
            print(f"Error setting up video player: {e}")
            self.setup_video_preview(video_path)
    
    def display_video_thumbnail_simple(self, video_path: Path):
        """Display simple video thumbnail with enhanced first frame extraction."""
        thumbnail_created = False
        
        try:
            cap = cv2.VideoCapture(str(video_path))
            
            # Try to get a few frames in case the first one is blank
            for frame_num in range(5):  # Try first 5 frames
                cap.set(cv2.CAP_PROP_POS_FRAMES, frame_num)
                ret, frame = cap.read()
                
                if ret and frame is not None:
                    # Check if frame is not completely black (common issue with first frames)
                    gray_frame = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
                    if cv2.mean(gray_frame)[0] > 10:  # Frame has some content
                        # Convert BGR to RGB
                        frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                        
                        # Apply video rotation if set
                        if hasattr(self, 'video_rotation') and self.video_rotation != 0:
                            if self.video_rotation == 90:
                                frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_90_CLOCKWISE)
                            elif self.video_rotation == 180:
                                frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_180)
                            elif self.video_rotation == 270:
                                frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_90_COUNTERCLOCKWISE)
                        
                        # Resize to fit preview area while maintaining aspect ratio
                        h, w = frame_rgb.shape[:2]
                        max_w, max_h = IMAGE_MAX
                        aspect_ratio = w / h
                        
                        if aspect_ratio > max_w / max_h:
                            new_w = max_w
                            new_h = int(max_w / aspect_ratio)
                        else:
                            new_h = max_h
                            new_w = int(max_h * aspect_ratio)
                        
                        # Ensure minimum size
                        new_w = max(new_w, 100)
                        new_h = max(new_h, 100)
                        
                        frame_resized = cv2.resize(frame_rgb, (new_w, new_h))
                        pil_image = Image.fromarray(frame_resized)
                        
                        # Add a subtle border to indicate it's a video thumbnail
                        from PIL import ImageDraw
                        draw = ImageDraw.Draw(pil_image)
                        draw.rectangle([0, 0, new_w-1, new_h-1], outline='#444444', width=2)
                        
                        # Add a small play icon overlay
                        try:
                            # Simple triangle play icon
                            play_size = 30
                            center_x, center_y = new_w // 2, new_h // 2
                            triangle = [
                                (center_x - play_size//2, center_y - play_size//2),
                                (center_x - play_size//2, center_y + play_size//2),
                                (center_x + play_size//2, center_y)
                            ]
                            draw.polygon(triangle, fill='white', outline='black')
                        except Exception:
                            pass  # Skip play icon if drawing fails
                        
                        self.tk_img = ImageTk.PhotoImage(pil_image)
                        self.preview_lbl.configure(image=self.tk_img, text="")
                        self.preview_lbl.pack(anchor="center")
                        thumbnail_created = True
                        break
                        
            cap.release()
                
        except Exception as e:
            print(f"Error creating video thumbnail: {e}")
            
        if not thumbnail_created:
            # Enhanced fallback with video icon
            try:
                from PIL import Image, ImageDraw, ImageFont
                img = Image.new('RGB', IMAGE_MAX, color='#f0f0f0')
                draw = ImageDraw.Draw(img)
                
                # Draw video icon background
                icon_size = 80
                center_x, center_y = IMAGE_MAX[0] // 2, IMAGE_MAX[1] // 2
                draw.rectangle([center_x - icon_size, center_y - icon_size, 
                               center_x + icon_size, center_y + icon_size], 
                               fill='#333333', outline='#666666', width=2)
                
                # Draw play triangle
                triangle = [
                    (center_x - 30, center_y - 40),
                    (center_x - 30, center_y + 40),
                    (center_x + 40, center_y)
                ]
                draw.polygon(triangle, fill='white')
                
                # Add filename
                try:
                    font = ImageFont.truetype("Arial.ttf", 14)
                except:
                    font = ImageFont.load_default()
                
                filename_text = video_path.name
                if len(filename_text) > 30:
                    filename_text = filename_text[:27] + "..."
                
                draw.text((center_x, center_y + icon_size + 20), filename_text, 
                         fill='black', font=font, anchor='mm')
                draw.text((center_x, center_y + icon_size + 40), "🎬 VIDEO", 
                         fill='#666666', font=font, anchor='mm')
                
                self.tk_img = ImageTk.PhotoImage(img)
                self.preview_lbl.configure(image=self.tk_img, text="")
                self.preview_lbl.pack(anchor="center")
                
            except Exception:
                # Final text fallback
                self.preview_lbl.configure(image=self.default_img, 
                                         text=f"🎬 VIDEO\n{video_path.name}")
                self.preview_lbl.pack(anchor="center")
    
    def play_video_vlc(self, video_path: Path):
        """Play video using system default player."""
        # Always use external player for reliable playback with audio
        self.launch_external_player(video_path)
        self.video_playing = True
        print(f"Launched video in default player: {video_path.name}")
    
    def stop_video_vlc(self):
        """Stop VLC video playback."""
        if hasattr(self, 'vlc_player') and self.vlc_player:
            try:
                self.vlc_player.stop()
                self.video_playing = False
            except Exception as e:
                print(f"Error stopping VLC: {e}")
    
    def set_vlc_volume(self, value):
        """Set VLC volume."""
        if hasattr(self, 'vlc_player') and self.vlc_player:
            try:
                volume = int(float(value))
                self.vlc_player.audio_set_volume(volume)
            except Exception as e:
                print(f"Error setting VLC volume: {e}")
    
    def setup_video_audio_pygame(self, video_path: Path):
        """Extract and setup audio using moviepy and pygame."""
        if not has_audio_support:
            return
        
        try:
            import tempfile
            import os
            
            # Extract audio to temporary file
            video_clip = mp.VideoFileClip(str(video_path))
            if video_clip.audio is not None:
                # Create temporary audio file
                temp_dir = tempfile.gettempdir()
                audio_filename = f"temp_audio_{os.getpid()}_{hash(str(video_path))}.wav"
                self.audio_file = os.path.join(temp_dir, audio_filename)
                
                # Extract audio
                video_clip.audio.write_audiofile(self.audio_file, verbose=False, logger=None)
                video_clip.close()
                
                print(f"Audio extracted to: {self.audio_file}")
            else:
                print("No audio track found in video")
                
        except Exception as e:
            print(f"Error extracting audio: {e}")
            self.audio_file = None
    
    def play_audio_pygame(self, start_time=0):
        """Start audio playback with pygame."""
        if not has_pygame or not self.audio_file or not os.path.exists(self.audio_file):
            return
        
        try:
            pygame.mixer.music.load(self.audio_file)
            pygame.mixer.music.play(start=start_time)
            self.audio_start_time = time.time() - start_time
            
            # Set volume
            volume = self.volume_var.get() / 100.0
            pygame.mixer.music.set_volume(volume)
            
        except Exception as e:
            print(f"Error playing audio: {e}")
    
    def stop_audio_pygame(self):
        """Stop audio playback."""
        if has_pygame:
            try:
                pygame.mixer.music.stop()
            except:
                pass
    
    def pause_audio_pygame(self):
        """Pause audio playback."""
        if has_pygame:
            try:
                pygame.mixer.music.pause()
            except:
                pass
    
    def unpause_audio_pygame(self):
        """Resume audio playback."""
        if has_pygame:
            try:
                pygame.mixer.music.unpause()
            except:
                pass
    
    def set_video_volume(self, value):
        """Set video audio volume."""
        if has_pygame:
            try:
                volume = float(value) / 100.0
                pygame.mixer.music.set_volume(volume)
            except:
                pass
    
    def cleanup_audio_file(self):
        """Clean up temporary audio file."""
        if self.audio_file and os.path.exists(self.audio_file):
            try:
                os.remove(self.audio_file)
                self.audio_file = None
            except:
                pass

    def play_audio_file(self, audio_path: Path):
        """Play audio file using system default player with embedded controls."""
        try:
            # For now, launch in system default player
            # TODO: Add embedded audio player using pygame or similar
            if hasattr(self, 'current_audio_process') and self.current_audio_process:
                try:
                    self.current_audio_process.terminate()
                    self.current_audio_process.wait(timeout=2)
                except:
                    try:
                        self.current_audio_process.kill()
                    except:
                        pass
            
            # Launch audio in default player
            self.current_audio_process = open_with_default_app(str(audio_path), self)
            
            # Update controls to show playing state
            for widget in self.music_controls.winfo_children():
                if isinstance(widget, ttk.Button) and "Play Audio" in widget.cget("text"):
                    widget.configure(text="🎵 Playing...")
                    # Reset button text after a delay
                    self.after(3000, lambda: widget.configure(text="🎵 Play Audio"))
                    break
                    
            print(f"Playing audio: {audio_path.name}")
            
        except Exception as e:
            messagebox.showerror("Audio Error", f"Could not play audio file:\n{e}")

    def create_album_art_thumbnail(self, music_path: Path):
        """Create and display album art thumbnail placeholder."""
        try:
            print(f"DEBUG: Creating album art thumbnail for {music_path.name}")
            # Create album art frame if it doesn't exist
            if not hasattr(self, 'album_art_frame'):
                self.album_art_frame = ttk.Frame(self.music_controls)
                print("DEBUG: Created new album_art_frame")
            else:
                # Clear existing album art
                for widget in self.album_art_frame.winfo_children():
                    widget.destroy()
                print("DEBUG: Cleared existing album art widgets")
            
            self.album_art_frame.pack(side="left", padx=10)
            print("DEBUG: Album art frame packed")
            
            # TODO: Extract actual album art from music file
            # For now, create a placeholder thumbnail
            from PIL import Image, ImageDraw, ImageFont
            
            # Create a small album art placeholder
            img = Image.new('RGB', (80, 80), color='lightgray')
            draw = ImageDraw.Draw(img)
            
            # Draw a simple music note symbol
            draw.rectangle([10, 10, 70, 70], outline='darkgray', width=2)
            draw.text((25, 30), "♪", fill='black', font=None)
            
            # Convert to PhotoImage and display
            self.album_art_img = ImageTk.PhotoImage(img)
            album_art_label = ttk.Label(self.album_art_frame, image=self.album_art_img)
            album_art_label.pack()
            
            # Add label below thumbnail
            ttk.Label(self.album_art_frame, text="Album Art", font=("Arial", 8)).pack()
            
        except Exception as e:
            print(f"Could not create album art thumbnail: {e}")
            # Create simple text placeholder
            ttk.Label(self.album_art_frame, text="[Album Art]").pack()

    def display_current_frame(self):
        """Display the current frame on the canvas."""
        if not hasattr(self, 'cap') or not self.cap or not self.cap.isOpened():
            return
        
        try:
            # Set frame position
            self.cap.set(cv2.CAP_PROP_POS_FRAMES, self.current_frame)
            ret, frame = self.cap.read()
            
            if ret:
                # Convert BGR to RGB
                frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                
                # Apply rotation if needed
                if self.video_rotation != 0:
                    if self.video_rotation == 90:
                        frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_90_CLOCKWISE)
                    elif self.video_rotation == 180:
                        frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_180)
                    elif self.video_rotation == 270:
                        frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_90_COUNTERCLOCKWISE)
                
                # Resize to fit canvas
                h, w = frame_rgb.shape[:2]
                canvas_w, canvas_h = VIDEO_MAX
                
                # Calculate scaling to maintain aspect ratio
                scale = min(canvas_w / w, canvas_h / h)
                new_w, new_h = int(w * scale), int(h * scale)
                
                # Resize frame
                frame_resized = cv2.resize(frame_rgb, (new_w, new_h))
                
                # Convert to PIL Image and then to PhotoImage
                pil_image = Image.fromarray(frame_resized)
                self.video_image = ImageTk.PhotoImage(pil_image)
                
                # Clear canvas and display frame
                self.video_canvas.delete("all")
                x = (canvas_w - new_w) // 2
                y = (canvas_h - new_h) // 2
                self.video_canvas.create_image(x, y, anchor="nw", image=self.video_image)
                
                # Update progress bar and time
                self.progress_var.set(self.current_frame)
                self.update_time_display()
                
        except Exception as e:
            print(f"Error displaying frame: {e}")
    
    def video_play_pause(self):
        """Toggle play/pause state."""
        if self.video_playing:
            self.video_paused = not self.video_paused
            if self.video_paused:
                self.pause_audio_pygame()
            else:
                self.unpause_audio_pygame()
        else:
            self.video_playing = True
            self.video_paused = False
            # Start audio from current position
            current_seconds = self.current_frame / self.fps
            self.play_audio_pygame(current_seconds)
            self.play_video_loop()
    
    def video_stop(self):
        """Stop video playback and return to first frame."""
        self.video_playing = False
        self.video_paused = False
        self.current_frame = 0
        self.stop_audio_pygame()
        self.display_current_frame()
    
    def video_rewind(self):
        """Rewind video by 10 seconds."""
        frames_to_rewind = int(self.fps * 10)  # 10 seconds
        self.current_frame = max(0, self.current_frame - frames_to_rewind)
        self.display_current_frame()
        # Restart audio from new position if playing
        if self.video_playing and not self.video_paused:
            current_seconds = self.current_frame / self.fps
            self.stop_audio_pygame()
            self.play_audio_pygame(current_seconds)
    
    def video_fast_forward(self):
        """Fast forward video by 10 seconds."""
        frames_to_forward = int(self.fps * 10)  # 10 seconds
        self.current_frame = min(self.total_frames - 1, self.current_frame + frames_to_forward)
        self.display_current_frame()
        # Restart audio from new position if playing
        if self.video_playing and not self.video_paused:
            current_seconds = self.current_frame / self.fps
            self.stop_audio_pygame()
            self.play_audio_pygame(current_seconds)
    
    def seek_video(self, value):
        """Seek to specific frame position."""
        try:
            self.current_frame = int(float(value))
            self.display_current_frame()
            # Restart audio from new position if playing
            if self.video_playing and not self.video_paused:
                current_seconds = self.current_frame / self.fps
                self.stop_audio_pygame()
                self.play_audio_pygame(current_seconds)
        except:
            pass
    
    def play_video_loop(self):
        """Main video playback loop."""
        if not self.video_playing or self.video_paused:
            return
        
        if self.current_frame >= self.total_frames - 1:
            # End of video
            self.video_stop()
            return
        
        self.current_frame += 1
        self.display_current_frame()
        
        # Schedule next frame
        self.after(self.frame_delay, self.play_video_loop)
    
    def update_time_display(self):
        """Update the time display label."""
        try:
            current_seconds = self.current_frame / self.fps
            total_seconds = self.total_frames / self.fps
            
            current_time = f"{int(current_seconds // 60):02d}:{int(current_seconds % 60):02d}"
            total_time = f"{int(total_seconds // 60):02d}:{int(total_seconds % 60):02d}"
            
            self.time_label.configure(text=f"{current_time} / {total_time}")
        except:
            self.time_label.configure(text="00:00 / 00:00")
    
    def toggle_fullscreen(self, event=None):
        """Toggle fullscreen video display."""
        if self.is_fullscreen:
            self.exit_fullscreen()
        else:
            self.enter_fullscreen()
    
    def enter_fullscreen(self):
        """Enter fullscreen mode."""
        if not hasattr(self, 'cap') or not self.cap:
            return
        
        self.is_fullscreen = True
        
        # Create fullscreen window
        self.fullscreen_window = tk.Toplevel(self)
        self.fullscreen_window.attributes('-fullscreen', True)
        self.fullscreen_window.configure(bg='black')
        self.fullscreen_window.bind('<Escape>', self.exit_fullscreen)
        self.fullscreen_window.bind('<Double-Button-1>', self.exit_fullscreen)
        
        # Create fullscreen canvas
        screen_width = self.fullscreen_window.winfo_screenwidth()
        screen_height = self.fullscreen_window.winfo_screenheight()
        
        self.fullscreen_canvas = tk.Canvas(
            self.fullscreen_window,
            width=screen_width,
            height=screen_height,
            bg='black',
            highlightthickness=0
        )
        self.fullscreen_canvas.pack(fill="both", expand=True)
        
        # Display current frame in fullscreen
        self.display_fullscreen_frame()
    
    def exit_fullscreen(self, event=None):
        """Exit fullscreen mode."""
        if hasattr(self, 'fullscreen_window') and self.fullscreen_window:
            self.fullscreen_window.destroy()
            self.fullscreen_window = None
        self.is_fullscreen = False
    
    def display_fullscreen_frame(self):
        """Display frame in fullscreen mode."""
        if not self.is_fullscreen or not hasattr(self, 'fullscreen_canvas'):
            return
        
        try:
            # Get current frame
            self.cap.set(cv2.CAP_PROP_POS_FRAMES, self.current_frame)
            ret, frame = self.cap.read()
            
            if ret:
                # Convert and apply rotation
                frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                
                if self.video_rotation != 0:
                    if self.video_rotation == 90:
                        frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_90_CLOCKWISE)
                    elif self.video_rotation == 180:
                        frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_180)
                    elif self.video_rotation == 270:
                        frame_rgb = cv2.rotate(frame_rgb, cv2.ROTATE_90_COUNTERCLOCKWISE)
                
                # Scale to screen size
                h, w = frame_rgb.shape[:2]
                screen_w = self.fullscreen_canvas.winfo_width()
                screen_h = self.fullscreen_canvas.winfo_height()
                
                scale = min(screen_w / w, screen_h / h)
                new_w, new_h = int(w * scale), int(h * scale)
                
                frame_resized = cv2.resize(frame_rgb, (new_w, new_h))
                pil_image = Image.fromarray(frame_resized)
                self.fullscreen_image = ImageTk.PhotoImage(pil_image)
                
                # Display centered
                self.fullscreen_canvas.delete("all")
                x = (screen_w - new_w) // 2
                y = (screen_h - new_h) // 2
                self.fullscreen_canvas.create_image(x, y, anchor="nw", image=self.fullscreen_image)
                
        except Exception as e:
            print(f"Error displaying fullscreen frame: {e}")

    def display_video_thumbnail(self, video_path):
        """Displays the first non-blank frame of a video as a thumbnail, with rotation."""
        if not has_cv2 or not hasattr(self, 'video_canvas'):
            return

        try:
            cap = cv2.VideoCapture(str(video_path))
            frame = None
            frame_found = False
            
            # Try to get first non-blank frame (up to first 10 frames)
            for frame_num in range(10):
                cap.set(cv2.CAP_PROP_POS_FRAMES, frame_num)
                ret, temp_frame = cap.read()
                
                if ret and temp_frame is not None:
                    # Check if frame is not completely black/blank
                    gray_frame = cv2.cvtColor(temp_frame, cv2.COLOR_BGR2GRAY)
                    if cv2.mean(gray_frame)[0] > 10:  # Frame has some content
                        frame = temp_frame
                        frame_found = True
                        break
            
            cap.release()

            if frame_found and frame is not None:
                # Apply rotation
                if self.video_rotation != 0:
                    (h, w) = frame.shape[:2]
                    center = (w / 2, h / 2)
                    M = cv2.getRotationMatrix2D(center, -self.video_rotation, 1.0)
                    new_dim = (w,h) if self.video_rotation == 180 else (h,w)
                    frame = cv2.warpAffine(frame, M, new_dim)

                frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                img = Image.fromarray(frame)
                img.thumbnail(VIDEO_MAX, Image.LANCZOS)
                
                photo = ImageTk.PhotoImage(image=img)
                self.video_canvas.delete("all")
                self.video_canvas.create_image(VIDEO_MAX[0]//2, VIDEO_MAX[1]//2, image=photo, anchor='center')
                self.video_canvas.image = photo # Keep a reference
            else:
                # No suitable frame found, show placeholder
                self.video_canvas.delete("all")
                self.video_canvas.create_text(VIDEO_MAX[0]//2, VIDEO_MAX[1]//2, 
                                            text=f"🎬 VIDEO\n{video_path.name}\n\nNo preview available", 
                                            fill="white", anchor='center', font=("Arial", 12))
        except Exception as e:
            print(f"Error creating video thumbnail: {e}")
            # Show error message on canvas
            if hasattr(self, 'video_canvas'):
                self.video_canvas.delete("all")
                self.video_canvas.create_text(VIDEO_MAX[0]//2, VIDEO_MAX[1]//2, 
                                            text=f"🎬 VIDEO\n{video_path.name}\n\nPreview error", 
                                            fill="white", anchor='center', font=("Arial", 12))

    def setup_video_audio(self, video_path: Path):
        """Setup VLC for audio playback with OpenCV video."""
        if has_vlc and self.vlc_instance:
            try:
                self.vlc_media = self.vlc_instance.media_new(str(video_path))
                self.vlc_player = self.vlc_instance.media_player_new()
                self.vlc_player.set_media(self.vlc_media)
                # Set VLC to audio-only mode
                if sys.platform.startswith("linux"):
                    self.vlc_player.set_xwindow(0)
                elif sys.platform.startswith("win32"):
                    self.vlc_player.set_hwnd(0)
                elif sys.platform.startswith("darwin"):
                     # On macOS, there is no simple way to hide the window.
                     # This will remain a known limitation.
                    pass

                print("VLC audio setup successful")
            except Exception as e:
                print(f"VLC audio setup failed: {e}")

    def launch_external_player(self, video_path: Path):
        """Launch the video in the system's default player."""
        try:
            # Kill any existing external video process first
            if hasattr(self, 'current_video_process') and self.current_video_process:
                try:
                    self.current_video_process.terminate()
                    self.current_video_process.wait(timeout=2)
                except:
                    try:
                        self.current_video_process.kill()
                    except:
                        pass
            
            # Launch external player
            self.current_video_process = open_with_default_app(str(video_path), self)
            print(f"Launched external player for: {video_path.name}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to launch video player: {e}")

    def setup_system_player(self, video_path: Path):
        """Set up a button to open the video in the system's default player."""
        self.video_frame = ttk.Frame(self.preview_frame)
        self.video_frame.pack(anchor="center", fill="both", expand=True)

        # A canvas to show thumbnail or placeholder
        self.video_canvas = tk.Canvas(self.video_frame, width=VIDEO_MAX[0], height=VIDEO_MAX[1], bg="black")
        self.video_canvas.pack()
        self.display_video_thumbnail(video_path)

        # Controls
        self.video_controls = ttk.Frame(self.preview_frame)
        self.video_controls.pack(fill="x", pady=5)
        
        ttk.Label(self.video_controls, text="Embedded player not available.").pack(side="left", padx=5)
        ttk.Button(self.video_controls, text="Open in Default Player",
                  command=lambda: self.launch_external_player(video_path)).pack(side="right", padx=5)

    def play_video(self):
        """Play the current video with audio."""
        if not self.current_video_path:
            return
        
        # TkVideoPlayer (has built-in audio)
        if has_tkvideoplayer and self.video_player:
            self.video_player.play()
            self.video_playing = True
            return
            
        # OpenCV + VLC audio combination
        if hasattr(self, 'video_canvas') and self.video_canvas:
            self.video_playing = True
            
            # Start VLC audio
            if hasattr(self, 'vlc_player') and self.vlc_player:
                self.vlc_player.play()
            
            # Start OpenCV video
            self.play_video_cv2()
            
    def pause_video(self):
        """Pause the current video."""
        # VLC player
        if hasattr(self, 'vlc_player') and self.vlc_player:
            self.vlc_player.pause()
            self.video_playing = False # for CV2 loop
            return
            
        # TkVideoPlayer
        if has_tkvideoplayer and self.video_player:
            self.video_player.pause()
            self.video_playing = False
            
            # Pause pygame audio if available
            if hasattr(self, 'pygame_player') and self.pygame_player:
                pygame.mixer.pause()
            return
            
        # OpenCV with audio
        if self.video_playing:
            self.video_playing = False
            
            # Pause audio
            if hasattr(self, 'pygame_player') and self.pygame_player:
                pygame.mixer.pause()
            elif hasattr(self, 'pyglet_player') and self.pyglet_player:
                self.pyglet_player.pause()
            
    def stop_video(self):
        """Stop the current video and clean up resources."""
        self.video_playing = False
        self.video_paused = False
        
        # Stop pygame audio
        self.stop_audio_pygame()
        
        # Stop VLC video
        self.stop_video_vlc()
        
        # Exit fullscreen if active
        if hasattr(self, 'is_fullscreen') and self.is_fullscreen:
            self.exit_fullscreen()
        
        # Stop VLC audio
        if hasattr(self, 'vlc_player') and self.vlc_player:
            try:
                self.vlc_player.stop()
            except Exception as e:
                print(f"VLC stop error: {e}")
                
        # TkVideoPlayer cleanup
        if has_tkvideoplayer and self.video_player:
            try:
                self.video_player.stop()
            except Exception as e:
                print(f"TkVideoPlayer stop error: {e}")
                
        # OpenCV cleanup
        if hasattr(self, 'cap') and self.cap:
            try:
                self.cap.release()
                self.cap = None
            except Exception as e:
                print(f"OpenCV cap release error: {e}")
        
    def set_volume(self, value):
        """Set volume for video playback."""
        volume = int(float(value))
        
        # Set VLC volume
        if hasattr(self, 'vlc_player') and self.vlc_player:
            self.vlc_player.audio_set_volume(volume)
        
        # Set TkVideoPlayer volume if available
        if hasattr(self, 'video_player') and hasattr(self.video_player, 'set_volume'):
            try:
                # TkVideoPlayer volume is 0.0 to 1.0
                self.video_player.set_volume(volume / 100.0)
            except:
                pass
            
    def play_video_cv2(self):
        """Play video using OpenCV with proper aspect ratio and rotation."""
        if not has_cv2 or not self.current_video_path or not self.video_playing:
            return
        
        if hasattr(self, 'cap') and self.cap and self.cap.isOpened():
             self.cap.release()

        self.cap = cv2.VideoCapture(str(self.current_video_path))
        
        def update_frame():
            if not self.video_playing or not hasattr(self, 'cap') or not self.cap.isOpened():
                if hasattr(self, 'cap') and self.cap: self.cap.release()
                return

            ret, frame = self.cap.read()
            if ret:
                # Apply rotation if needed
                if self.video_rotation != 0:
                    (h, w) = frame.shape[:2]
                    center = (w / 2, h / 2)
                    M = cv2.getRotationMatrix2D(center, -self.video_rotation, 1.0)
                    new_dim = (w,h) if self.video_rotation == 180 else (h,w)
                    frame = cv2.warpAffine(frame, M, new_dim)

                frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                img = Image.fromarray(frame)
                img.thumbnail(VIDEO_MAX, Image.LANCZOS)
                
                photo = ImageTk.PhotoImage(image=img)
                
                if hasattr(self, 'video_canvas') and self.video_canvas.winfo_exists():
                    self.video_canvas.delete("all")
                    self.video_canvas.create_image(VIDEO_MAX[0]//2, VIDEO_MAX[1]//2, image=photo)
                    self.video_canvas.image = photo
                    
                    self.after(30, update_frame)  # ~33fps
            else:
                self.stop_video()
                # Optionally, reset to first frame thumbnail
                self.after(100, lambda: self.display_video_thumbnail(self.current_video_path))

        update_frame()
        
    def open_in_vlc(self, video_path: Path):
        """Open the video in VLC player."""
        # Stop any current playback
        self.stop_video()
        
        # Check if VLC is available
        vlc_path = None
        
        # Try to find VLC on different platforms
        if sys.platform == "win32":
            # Windows
            for path in [
                os.path.join(os.environ.get('PROGRAMFILES', ''), 'VideoLAN', 'VLC', 'vlc.exe'),
                os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'VideoLAN', 'VLC', 'vlc.exe')
            ]:
                if os.path.exists(path):
                    vlc_path = path
                    break
        elif sys.platform == "darwin":
            # macOS
            vlc_path = "/Applications/VLC.app/Contents/MacOS/VLC"
            if not os.path.exists(vlc_path):
                # Try Homebrew installation
                brew_vlc = "/usr/local/bin/vlc"
                if os.path.exists(brew_vlc):
                    vlc_path = brew_vlc
        else:
            # Linux
            vlc_path = "/usr/bin/vlc"
            if not os.path.exists(vlc_path):
                vlc_path = "/usr/local/bin/vlc"
                
        if vlc_path and os.path.exists(vlc_path):
            try:
                subprocess.Popen([vlc_path, str(video_path)])
            except Exception as e:
                messagebox.showerror("VLC Error", f"Failed to open VLC: {e}")
        else:
            messagebox.showinfo("VLC Not Found", 
                               "VLC player not found. Please install VLC or use the system default player.")
            self.launch_external_player(video_path)
        
    def open_in_default_player(self, video_path: Path):
        """Open the video in the system's default player."""
        if sys.platform == "win32":
            os.startfile(video_path)
        elif sys.platform == "darwin":  # macOS
            subprocess.call(["open", video_path])
        else:  # linux
            subprocess.call(["xdg-open", video_path])

    @staticmethod
    def _safe_json_list(text: str) -> List[str]:
        """Parse JSON text as a list, return empty list if invalid."""
        if not text: return []
        try:
            obj = json.loads(text)
            return obj if isinstance(obj, list) else [str(obj)]
        except (json.JSONDecodeError, TypeError):
            return [s.strip() for s in text.split(',') if s.strip()]
            
    @staticmethod
    def _safe_json_str(text: str) -> str:
        """Parse JSON text, handle both string and object types."""
        if not text: return ""
        try:
            obj = json.loads(text)
            return str(obj) if not isinstance(obj, str) else obj
        except (json.JSONDecodeError, TypeError):
            return text

    def on_save(self):
        if not self.current_file:
            return
        
        # Save based on current media type
        if self.current_media_type == "music":
            self.save_music_record()
        else:  # photo or video
            self.save_visual_record()
            
        # Refresh one line in tree - use title for music, description for others
        if self.current_media_type == "music":
            desc_value = self.title_var.get() or "Untitled"
        else:
            desc_value = getattr(self, 'desc_txt', None)
            if desc_value:
                desc_value = desc_value.get("1.0", "end").strip()
            else:
                desc_value = ""
        
        self.tree.set(self.current_file, column="desc", value=desc_value)
        messagebox.showinfo("Saved", f"Metadata for {self.current_file} saved.")

    def save_music_record(self):
        """Save music-specific fields to database using new schema fields."""
        # Get values from the new music form fields
        track_title = self.track_title_var.get().strip() if hasattr(self, 'track_title_var') else ""
        artist = self.artist_var.get().strip() if hasattr(self, 'artist_var') else ""
        album = self.album_var.get().strip() if hasattr(self, 'album_var') else ""
        moods = self.moods_var.get().strip() if hasattr(self, 'moods_var') else ""
        genre = self.genre_var.get().strip() if hasattr(self, 'genre_var') else ""
        year = self.year_var.get().strip() if hasattr(self, 'year_var') else ""
        track_number = self.track_number_var.get().strip() if hasattr(self, 'track_number_var') else ""
        rating_key = self.rating_key_var.get().strip() if hasattr(self, 'rating_key_var') else ""
        file_path = self.file_path_var.get().strip() if hasattr(self, 'file_path_var') else ""
        album_summary = self.album_summary_txt.get("1.0", "end").strip() if hasattr(self, 'album_summary_txt') else ""
        artist_summary = self.artist_summary_txt.get("1.0", "end").strip() if hasattr(self, 'artist_summary_txt') else ""
        summary = self.summary_txt.get("1.0", "end").strip() if hasattr(self, 'summary_txt') else ""
        bitrate = self.bitrate_var.get().strip() if hasattr(self, 'bitrate_var') else ""
        codec = self.codec_var.get().strip() if hasattr(self, 'codec_var') else ""
        channels = self.channels_var.get().strip() if hasattr(self, 'channels_var') else ""
        container = self.container_var.get().strip() if hasattr(self, 'container_var') else ""
        
        # Convert numeric fields appropriately
        year_val = int(year) if year and year.isdigit() else None
        track_num_val = int(track_number) if track_number and track_number.isdigit() else None
        bitrate_val = int(bitrate) if bitrate and bitrate.isdigit() else None
        
        # Update database with all the new music fields
        cur = self.db.conn.cursor()
        cur.execute("""
            UPDATE media SET 
                description = ?, artist = ?, album = ?, moods = ?, genre = ?, year = ?, 
                track_number = ?, rating_key = ?, file_path = ?,
                album_summary = ?, artist_summary = ?, summary = ?, 
                bitrate = ?, codec = ?, channels = ?, container = ?,
                last_updated = datetime('now') 
            WHERE file_name = ?
        """, (
            track_title, artist, album, moods, genre, year_val,
            track_num_val, rating_key, file_path,
            album_summary, artist_summary, summary,
            bitrate_val, codec, channels, container,
            self.current_file
        ))
        self.db.conn.commit()

    def save_visual_record(self):
        """Save visual media fields to database."""
        keywords = [k.strip() for k in self.kw_var.get().split(",") if k.strip()]
        location_name = self.loc_var.get().strip() or "unknown"
        description = self.desc_txt.get("1.0", "end").strip()
        people = [p.strip() for p in self.people_var.get().split(",") if p.strip()]
        labels = [l.strip() for l in self.labels_var.get().split(",") if l.strip()]
        
        self.db.save_record(
            self.current_file, 
            keywords, 
            location_name, 
            description,
            people,
            labels
        )

    def open_full_editor(self):
        """Open a comprehensive editor window for all database fields."""
        if not self.current_file:
            messagebox.showwarning("Edit All Fields", "No file selected.")
            return
        
        # Get current record
        row = self.db.fetch_one(self.current_file)
        if not row:
            messagebox.showerror("Edit All Fields", "Could not load record from database.")
            return
        
        # Create full editor dialog
        editor = tk.Toplevel(self)
        editor.title(f"Edit All Fields - {self.current_file}")
        editor.geometry("600x500")
        editor.transient(self)
        editor.grab_set()
        
        # Create scrollable frame
        canvas = tk.Canvas(editor)
        scrollbar = ttk.Scrollbar(editor, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # All database fields - show different fields based on media type
        fields = {}
        
        # Determine media type from current record
        media_type = row["media_type"].lower() if row["media_type"] else ""
        
        if media_type == "music":
            # Music-specific fields (exclude image/video fields)
            field_names = [
                ("id", "ID"),
                ("file_name", "File Name"),
                ("media_type", "Media Type"),
                ("date_original", "Date Original"),
                ("genre", "Genre"),
                ("duration", "Duration"),
                ("file_path", "File Path"),
                ("file_size", "File Size"),
                ("file_ext", "File Extension"),
                ("description", "Track Title"),
                ("date_added", "Date Added"),
                ("last_updated", "Last Updated"),
                ("rating_key", "Rating Key"),
                ("artist", "Artist"),
                ("album", "Album"),
                ("moods", "Moods"),
                ("year", "Year"),
                ("album_summary", "Album Summary"),
                ("artist_summary", "Artist Summary"),
                ("summary", "Summary"),
                ("bitrate", "Bitrate"),
                ("codec", "Codec"),
                ("channels", "Channels"),
                ("container", "Container")
            ]
        else:
            # Photo/Video fields (exclude music-specific fields)
            field_names = [
                ("id", "ID"),
                ("file_name", "File Name"),
                ("media_type", "Media Type"),
                ("date_original", "Date Original"),
                ("keywords", "Keywords"),
                ("genre", "Genre"),
                ("duration", "Duration"),
                ("file_path", "File Path"),
                ("file_size", "File Size"),
                ("file_ext", "File Extension"),
                ("width", "Width"),
                ("height", "Height"),
                ("tags", "Tags"),
                ("people", "People"),
                ("location_name", "Location Name"),
                ("location", "Location"),
                ("latitude", "Latitude"),
                ("longitude", "Longitude"),
                ("labels", "Labels"),
                ("description", "Description"),
                ("date_added", "Date Added"),
                ("last_updated", "Last Updated"),
                ("rating_key", "Rating Key")
            ]
        
        row_num = 0
        for field_key, field_label in field_names:
            ttk.Label(scrollable_frame, text=f"{field_label}:", width=15, anchor="e").grid(
                row=row_num, column=0, sticky="w", pady=2, padx=(10, 5))
            
            if field_key in ["description", "album_summary", "artist_summary", "summary"]:
                # Multi-line text for description and summary fields
                var = tk.Text(scrollable_frame, width=50, height=3, wrap="word")
                var.insert("1.0", str(row[field_key] or ""))
                var.grid(row=row_num, column=1, sticky="w", pady=2)
            else:
                # Single-line entry
                var = tk.StringVar()
                var.set(str(row[field_key] or ""))
                entry = ttk.Entry(scrollable_frame, textvariable=var, width=50)
                entry.grid(row=row_num, column=1, sticky="w", pady=2)
                var = var  # Store the StringVar
            
            fields[field_key] = var
            row_num += 1
        
        # Buttons
        btn_frame = ttk.Frame(editor)
        btn_frame.pack(side="bottom", fill="x", padx=10, pady=10)
        
        def save_all():
            try:
                cur = self.db.conn.cursor()
                # Build update query for all editable fields
                update_fields = []
                values = []
                
                for field_key in fields:
                    if field_key not in ["id", "date_added", "last_updated"]:  # Skip read-only fields
                        if field_key in ["description", "album_summary", "artist_summary", "summary"]:
                            value = fields[field_key].get("1.0", "end").strip()
                        else:
                            value = fields[field_key].get().strip()
                        update_fields.append(f"{field_key} = ?")
                        values.append(value if value else None)
                
                update_fields.append("last_updated = datetime('now')")
                values.append(self.current_file)
                
                query = f"UPDATE media SET {', '.join(update_fields)} WHERE file_name = ?"
                cur.execute(query, values)
                self.db.conn.commit()
                
                editor.destroy()
                messagebox.showinfo("Saved", "All fields updated successfully.")
                # Reload the current record
                self.load_record(self.current_file)
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save: {e}")
        
        ttk.Button(btn_frame, text="Cancel", command=editor.destroy).pack(side="right")
        ttk.Button(btn_frame, text="Save All", command=save_all).pack(side="right", padx=(0, 10))
        
        # Pack scrollable components
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

    # --------------------------------------------------------------------
    # Navigation
    # --------------------------------------------------------------------
    def on_next(self) -> None:
        """Select the next row in the Treeview (wraps to first at end)."""
        # First completely cleanup any media players
        self.stop_video()
        
        # current selection
        selected = self.tree.selection()
        if not selected:
            return
        cur_iid = selected[0]

        # find the next sibling; if none, wrap
        nxt = self.tree.next(cur_iid)
        if not nxt:
            all_items = self.tree.get_children()
            if not all_items:
                return
            nxt = all_items[0]

        # make it the current selection and load its metadata
        self.tree.selection_set(nxt)
        self.tree.see(nxt)
        self.load_record(nxt)
        
    def on_previous(self) -> None:
        """Select the previous row in the Treeview (wraps to last at beginning)."""
        # First completely cleanup any media players
        self.stop_video()
        
        # current selection
        selected = self.tree.selection()
        if not selected:
            return
        cur_iid = selected[0]

        # find the previous sibling; if none, wrap
        prev = self.tree.prev(cur_iid)
        if not prev:
            all_items = self.tree.get_children()
            if not all_items:
                return
            prev = all_items[-1]  # Get the last item

        # make it the current selection and load its metadata
        self.tree.selection_set(prev)
        self.tree.see(prev)
        self.load_record(prev)

    # --------------------------------------------------------------------
    # Shutdown
    # --------------------------------------------------------------------
    def on_closing(self):
        """Handle window close event with proper cleanup."""
        try:
            self.quit()
        except Exception as e:
            print(f"Error during cleanup: {e}")
            # Force close anyway
            self.destroy()

    def quit(self):
        """Clean up resources and exit."""
        print("🧹 Starting application cleanup...")
        
        # 1. Clean up queue manager and current temp playlists
        if hasattr(self, 'queue_manager') and self.queue_manager:
            try:
                if hasattr(self.queue_manager, 'current_temp_playlist') and self.queue_manager.current_temp_playlist:
                    print(f"Cleaning up temp playlist: {self.queue_manager.current_temp_playlist}")
                    self._cleanup_temp_playlist(self.queue_manager.current_temp_playlist)
                self.queue_manager.clear_queue_state()
                print("✓ Queue manager cleaned up")
            except Exception as e:
                print(f"Queue cleanup error: {e}")

        # 2. Stop any playing video or audio
        try:
            self.stop_video()
            print("✓ Video stopped")
        except Exception as e:
            print(f"Video stop error: {e}")

        # 3. Kill any external video process
        if hasattr(self, 'current_video_process') and self.current_video_process:
            try:
                self.current_video_process.terminate()
                self.current_video_process.wait(timeout=2)
                print("✓ Video process terminated")
            except:
                try:
                    self.current_video_process.kill()
                    print("✓ Video process killed")
                except:
                    print("⚠ Could not terminate video process")
        
        # 4. Kill any external audio process  
        if hasattr(self, 'current_audio_process') and self.current_audio_process:
            try:
                self.current_audio_process.terminate()
                self.current_audio_process.wait(timeout=2)
                print("✓ Audio process terminated")
            except:
                try:
                    self.current_audio_process.kill()
                    print("✓ Audio process killed")
                except:
                    print("⚠ Could not terminate audio process")
                
        # 5. Clean up pygame
        if has_pygame:
            try:
                pygame.mixer.quit()
                print("✓ Pygame mixer cleaned up")
            except:
                print("⚠ Pygame cleanup failed")
        
        # 6. Close images
        if hasattr(self, 'current_img') and self.current_img:
            try:
                self.current_img.close()
                print("✓ Current image closed")
            except:
                pass
        
        # 7. Close database connection
        try:
            self.db.conn.close()
            print("✓ Database connection closed")
        except Exception as e:
            print(f"Database close error: {e}")
        
        print("🧹 Cleanup completed")
        super().quit()

    # ────────────────────────────────────────────────────────────────────────
    #  DELETE  (new feature)
    # ────────────────────────────────────────────────────────────────────────
    def delete_selected_image(self) -> None:
        """Delete the selected image file *and* its DB row."""
        sel = self.tree.selection()
        if not sel:
            messagebox.showwarning("Delete", "No image selected.")
            return

        file_name = sel[0]                          # iid == file_name
        row = self.db.fetch_one(file_name)
        if row is None:
            # If not in DB, maybe it's just in the tree. Remove from tree.
            self.tree.delete(file_name)
            messagebox.showerror("Delete", "Record not found in database, removed from list.")
            return

        file_path_str = row["file_path"]
        if not file_path_str:
            messagebox.showerror("Delete", "File path is missing from the database record.")
            return
        
        file_path = Path(file_path_str)

        if not messagebox.askyesno(
            "Confirm Delete",
            f"Are you sure you want to permanently delete '{file_name}' and all its metadata?\n\nThis cannot be undone."
        ):
            return

        try:
            # 1) delete file from disk (ignore if missing)
            if file_path.exists():
                os.remove(file_path)
                print(f"Deleted file: {file_path}")
            else:
                 print(f"File not found on disk, but will delete DB record: {file_path}")

            # 2) delete database row
            cur = self.db.conn.cursor()
            cur.execute("DELETE FROM media WHERE file_name = ?", (file_name,))
            self.db.conn.commit()

            # 3) update UI
            self.tree.delete(file_name)
            self.clear_form()
            messagebox.showinfo("Delete", "Image and metadata deleted successfully.")
        except Exception as exc:
            messagebox.showerror("Delete", f"An error occurred while deleting:\n{exc}")

    def clear_form(self) -> None:
        """Reset preview/image fields after a delete."""
        self.stop_video()
        if self.video_player: self.video_player.destroy()
        if self.video_frame: self.video_frame.destroy()
        
        if self.current_img: self.current_img.close()
        self.current_img = None
        self.current_file = None

        self.preview_lbl.configure(image=self.default_img)
        
        # Clear all entry fields - need to check if they exist first
        self.fn_lbl.config(text="")
        self.id_lbl.config(text="")
        self.date_lbl.config(text="")
        self.loc_lbl.config(text="")
        
        # Clear form fields based on current form type
        if hasattr(self, 'current_media_type') and self.current_media_type == "music":
            if hasattr(self, 'title_var'): self.title_var.set("")
            if hasattr(self, 'artist_var'): self.artist_var.set("")
            if hasattr(self, 'album_var'): self.album_var.set("")
            if hasattr(self, 'genre_var'): self.genre_var.set("")
            if hasattr(self, 'date_released_var'): self.date_released_var.set("")
            if hasattr(self, 'rating_key_var'): self.rating_key_var.set("")
        else:
            if hasattr(self, 'kw_var'): self.kw_var.set("")
            if hasattr(self, 'loc_var'): self.loc_var.set("")
            if hasattr(self, 'people_var'): self.people_var.set("")
            if hasattr(self, 'labels_var'): self.labels_var.set("")
            if hasattr(self, 'desc_txt'): self.desc_txt.delete("1.0", "end")

    def on_select_database(self):
        """Open a small dialog with a dropdown of .db files in cwd."""
        self._open_db_dialog()

    def set_database(self, db_path: str):
        """Switch the active visuals database and reload the tree."""
        try:
            if hasattr(self, "db") and getattr(self.db, "conn", None):
                try: self.db.conn.close()
                except Exception: pass
        except Exception:
            pass
        # Recreate MetadataDB and refresh UI
        self.db = MetadataDB(db_path)
        save_state(current_db=db_path, current_media_kind="visuals")
        rows = self.db.fetch_all() if hasattr(self.db, "fetch_all") else []
        self._populate_tree(rows)

    def _open_db_dialog(self):
        win = tk.Toplevel(self)
        win.title("Select Database")
        win.transient(self)
        win.grab_set()

        ttk.Label(win, text=f"Databases in {os.getcwd()}").pack(padx=12, pady=(12,6), anchor="w")
        values = scan_dbs(os.getcwd())
        sel_var = tk.StringVar(value=(load_state().get("current_db") or (values[0] if values else "")))

        combo = ttk.Combobox(win, textvariable=sel_var, values=values, state="readonly", width=60)
        combo.pack(padx=12, pady=6, fill="x")

        btns = ttk.Frame(win)
        btns.pack(padx=12, pady=12, fill="x")
        ttk.Button(btns, text="Cancel", command=win.destroy).pack(side="right")
        def _ok():
            db_path = sel_var.get().strip()
            if not db_path or not Path(db_path).exists():
                messagebox.showwarning("Select Database", "Please select a valid .db file.")
                return
            kind = classify_db(db_path)
            if kind == "visuals":
                self.set_database(db_path)
            elif kind == "music":
                save_state(current_db=db_path, current_media_kind="music")
                messagebox.showinfo("Music DB", "Music editor UI not implemented yet – database selection saved.")
            else:
                messagebox.showwarning("Unknown DB", "Could not determine DB type (music vs visuals).")
            win.destroy()
        ttk.Button(btns, text="Open", command=_ok).pack(side="right", padx=(0,8))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    # Ensure the export directory exists
    PHOTOS_DIR.mkdir(exist_ok=True)
    app = MetadataEditorApp()
    app.mainloop()


if __name__ == "__main__":
    main()
