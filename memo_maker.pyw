"""Memo Maker, транскрибатор встреч: приложение в трее.

Следит за папкой, куда OBS пишет записи. Когда запись закончена, всплывает
окно с вопросом, нужно ли её обработать: имя файла с подставленной датой,
папка для результата, режим нагрузки на видеокарту и нужно ли мемо.
Встречи обрабатываются по одной в порядке очереди. Сначала идёт транскрибация
скриптом transcribe.py, затем по желанию мемо через Claude Code в режиме
командной строки. Claude запускается в папке "Проект для мемо": если там есть
скилл meeting-memo, мемо делается по нему. О каждом завершении приходит
уведомление Windows.

Последний шаг по желанию: сжатие записи в H.265 на видеокарте через ffmpeg.
Сжатый файл "<имя> (H.265).mp4" кладётся рядом с записью, оригинал по желанию
удаляется после проверки сжатого. Сжатие идёт после транскрибации, потому что
Whisper слушает только звук, а звук при сжатии копируется без изменений: текст
от порядка не зависит, а транскрипция и мемо приходят без задержки. Видеокарту
сжатие уступает: ждёт, пока OBS пишет новую запись или открыто окно новой
записи, и пропускает вперёд встречи, которым нужна транскрибация или мемо.
Если такое случилось посреди сжатия, ffmpeg останавливается, а сжатие потом
начинается заново.

Запуск без консольного окна:
    pyw -3.12 memo_maker.pyw

Пакеты перечислены в requirements.txt. Оформление повторяет светлую или
тёмную тему Windows. Ярлыки на рабочем столе, в меню "Пуск" и в автозагрузке
создаёт install.ps1. Настройки, список папок и очередь хранятся
в %APPDATA%/MeetingTranscriber/settings.json.
Закрытие окна прячет его в трей, выход через меню значка. Незаконченная
встреча при выходе возвращается в очередь и продолжается при следующем запуске.

Для мемо Claude Code должен быть авторизован: один раз запустить claude
в терминале и выполнить /login.
"""

from __future__ import annotations

import ctypes
import json
import os
import queue
import re
import shutil
import subprocess
import sys
import threading
import time
import tkinter as tk
import uuid
from collections import deque
from ctypes import wintypes
from datetime import datetime
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

import pystray
import sv_ttk
from PIL import Image, ImageDraw, ImageFont, ImageTk
from pystray._util import win32 as tray_win32

TITLE = "Memo Maker"
APP_ID = "MemoMaker.App"
APP_DIR = Path(__file__).resolve().parent
TRANSCRIBE = APP_DIR / "transcribe.py"
INSTALL_SCRIPT = APP_DIR / "install.ps1"
ICON = APP_DIR / "memo_maker.ico"
ICON_BUSY = APP_DIR / "memo_maker_busy.ico"
ICON_SIZES = (16, 20, 24, 32, 40, 48, 64, 96, 128, 256)
ICON_FONT = Path(os.environ.get("WINDIR", "C:/Windows")) / "Fonts" / "SegoeIcons.ttf"
DEFAULT_WATCH = Path.home() / "Videos"
DEFAULT_OUT = Path.home() / "Documents" / TITLE
SETTINGS_DIR = Path(os.environ.get("APPDATA", Path.home())) / "MeetingTranscriber"
SETTINGS = SETTINGS_DIR / "settings.json"
STARTUP_DIR = Path(os.environ.get("APPDATA", Path.home())) / "Microsoft/Windows/Start Menu/Programs/Startup"
STARTUP_LINK = STARTUP_DIR / f"{TITLE}.lnk"
OLD_STARTUP_LINK = STARTUP_DIR / "Транскрибатор встреч.lnk"

# значки на кнопках из шрифта Segoe Fluent Icons
GLYPHS = {"add": "\uE710", "up": "\uE74A", "mode": "\uE8AB", "retry": "\uE72C", "remove": "\uE711",
          "details": "\uE946", "open": "\uE8E5", "clear": "\uE74D", "folder": "\uE8B7", "new_folder": "\uE8F4",
          "minus": "\uE738", "play": "\uE768", "expanded": "\uE70D", "collapsed": "\uE76C",
          "transcript": "\uE8A5", "memo": "\uE70B"}

VIDEO_EXT = {".mp4", ".mkv", ".mov", ".webm", ".avi", ".flv"}
MEDIA_TYPES = [("Видео и аудио", "*.mp4 *.mkv *.mov *.webm *.avi *.flv *.m4a *.mp3 *.wav *.ogg"),
               ("Все файлы", "*.*")]
OBS_DATE = re.compile(r"(\d{4})-(\d{2})-(\d{2})")
PROGRESS = re.compile(r"^(\d+(?:\.\d+)?)%")
SCAN_MS = 5000
STABLE_SECONDS = 15
MEMO_TIMEOUT = 30 * 60
JOURNAL_LINES = 300
IDLE_GRADIENT = ((64, 156, 255), (79, 70, 229))
BUSY_GRADIENT = ((255, 166, 72), (234, 88, 12))

MODES = {"fast": "Быстро", "gentle": "Щадяще"}
STATUS = {"waiting": "в очереди", "transcribing": "транскрибация", "memo": "мемо", "compressing": "сжатие",
          "done": "готово", "error": "ошибка", "cancelled": "отменено"}
ACTIVE = ("transcribing", "memo", "compressing")
FINISHED = ("done", "error", "cancelled")

# Сжатие повторяет настройки скилла video-compress из Arch Clean Maker: запись созвона OBS в H.264
# при CQ 23 ужимается примерно до 10 % размера, на глаз как оригинал (проба 2026-10-03).
COMPRESSED_SUFFIX = " (H.265)"
COMPRESS_CQ = 23
MIN_SAVING = 0.25  # если сжатый файл меньше оригинала не на четверть, он удаляется, а оригинал остаётся
MODERN_CODECS = {"hevc": "уже H.265", "av1": "уже AV1", "vp9": "уже VP9"}
FFMPEG_TIME = re.compile(r"^out_time_us=(\d+)")
FFMPEG_SPEED = re.compile(r"^speed=\s*([\d.]+)x")
FFMPEG_KEY = re.compile(r"^\w+=")
COMPRESS_CHECK_SECONDS = 2
QUEUE = "в очереди встреча, которой нужна транскрибация или мемо"  # сжатие ей уступает

CLAUDE_TOOLS = "Read,Write,Edit,Glob,Grep,Skill"
LOGIN_HINT = "Claude Code не авторизован: запустите claude в терминале и выполните /login."
MEMO_PROMPT = """Сделай мемо по транскрипции встречи. Если в проекте есть скилл meeting-memo, работай по нему. Если скилла нет, оформи мемо в Markdown: тема, контекст, принятые решения, открытые вопросы, задачи с ответственными.

Транскрипция: {transcript}
Мемо сохрани в ту же папку: {folder}

Других файлов не создавай и не меняй, ничего не публикуй.
В ответе дай имя сохранённого файла и то, что правила проекта велят сообщить после мемо."""

CREATE_NO_WINDOW = 0x08000000
BELOW_NORMAL_PRIORITY_CLASS = 0x4000
GENERIC_READ = 0x80000000
OPEN_EXISTING = 3
ERROR_ALREADY_EXISTS = 183

if os.name == "nt":
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.CreateFileW.restype = wintypes.HANDLE
    kernel32.CreateFileW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, wintypes.LPVOID,
                                     wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE]
    kernel32.CreateMutexW.restype = wintypes.HANDLE
    INVALID_HANDLE = wintypes.HANDLE(-1).value


def is_busy(path: Path) -> bool:
    """Файл открыт другим процессом, например OBS ещё пишет запись."""
    if os.name != "nt":
        return False
    handle = kernel32.CreateFileW(str(path), GENERIC_READ, 0, None, OPEN_EXISTING, 0, None)
    if handle == INVALID_HANDLE:
        return True
    kernel32.CloseHandle(handle)
    return False


def single_instance() -> bool:
    if os.name != "nt":
        return True
    global _mutex
    _mutex = kernel32.CreateMutexW(None, False, "Local\\MeetingTranscriber")
    return ctypes.get_last_error() != ERROR_ALREADY_EXISTS


def list_videos(folder: Path) -> list[str]:
    """Записи в папке. Сжатые копии "<имя> (H.265).mp4" новыми записями не считаются."""
    try:
        return [str(p) for p in folder.iterdir()
                if p.is_file() and p.suffix.lower() in VIDEO_EXT and not p.stem.endswith(COMPRESSED_SUFFIX)]
    except OSError:
        return []


def compressed_path(video: Path) -> Path:
    return video.with_name(f"{video.stem}{COMPRESSED_SUFFIX}.mp4")


def has_file(job: dict, key: str) -> bool:
    return bool(job.get(key)) and Path(job[key]).exists()


def compression_pending(job: dict) -> bool:
    return bool(job.get("compress")) and not has_file(job, "compressed") and not job.get("compress_skip")


def compression_only(job: dict) -> bool:
    """Транскрипция и мемо у встречи готовы, осталось только сжатие."""
    return has_file(job, "transcript") and (not job["memo"] or has_file(job, "memo_file"))


def probe_media(ffprobe: str, path: Path) -> dict | None:
    """Кодек и номер видеодорожки, длительность и кодеки звука по ffprobe. None, если файл не читается."""
    result = subprocess.run([ffprobe, "-v", "error", "-show_entries",
                             "format=duration:stream=codec_type,codec_name,pix_fmt:stream_disposition=attached_pic",
                             "-of", "json", str(path)],
                            capture_output=True, text=True, encoding="utf-8", errors="replace",
                            creationflags=CREATE_NO_WINDOW)
    try:
        data = json.loads(result.stdout)
        duration = float(data["format"]["duration"])
    except (ValueError, KeyError, TypeError):
        return None
    streams = data.get("streams", [])
    videos = [s for s in streams if s.get("codec_type") == "video"]
    # обложка в MP4 тоже видеодорожка, её не сжимаем
    video = next((s for s in videos if not (s.get("disposition") or {}).get("attached_pic")), None)
    return {"duration": duration, "codec": video["codec_name"] if video else "",
            "pix_fmt": video.get("pix_fmt", "") if video else "", "video_index": videos.index(video) if video else 0,
            "audio": [s.get("codec_name", "") for s in streams if s.get("codec_type") == "audio"]}


def compress_cmd(ffmpeg: str, video: Path, target: Path, info: dict) -> list[str]:
    """Сжатие в H.265 на видеокарте. Звук AAC копируется как есть, другой звук переводится в AAC."""
    ten_bit = "10" in info["pix_fmt"]
    cmd = [ffmpeg, "-hide_banner", "-nostdin", "-v", "error", "-y", "-i", str(video),
           "-map", f"0:v:{info['video_index']}"]
    for index, codec in enumerate(info["audio"]):
        cmd += ["-map", f"0:a:{index}", f"-c:a:{index}"]
        cmd += ["copy"] if codec == "aac" else ["aac", f"-b:a:{index}", "192k"]
    return cmd + ["-fps_mode", "passthrough", "-c:v", "hevc_nvenc", "-preset", "p7", "-tune", "hq", "-rc", "vbr",
                  "-cq", str(COMPRESS_CQ), "-b:v", "0", "-maxrate", "200M", "-bufsize", "400M", "-spatial-aq", "1",
                  "-pix_fmt", "p010le" if ten_bit else "yuv420p", "-profile:v", "main10" if ten_bit else "main",
                  "-tag:v", "hvc1", "-map_metadata", "0", "-movflags", "+faststart+use_metadata_tags",
                  "-f", "mp4", "-progress", "pipe:1", "-nostats", str(target)]


def same_duration(info: dict | None, duration: float) -> bool:
    return bool(info) and abs(info["duration"] - duration) <= max(1.0, duration * 0.01)


def default_name(video: Path) -> str:
    match = OBS_DATE.search(video.stem)
    date = " ".join(match.groups()) if match else datetime.now().strftime("%Y %m %d")
    return date + " "


def sanitize(name: str) -> str:
    return re.sub(r'[<>:"/\\|?*]+', "_", name).strip().rstrip(". ")


def describe(video: Path) -> str:
    parts = []
    try:
        import av
        with av.open(str(video)) as container:
            if container.duration:
                parts.append(f"{container.duration / 1_000_000 / 60:.0f} мин")
    except Exception:  # длительность только для справки, без неё окно тоже работает
        pass
    parts.append(size_text(video.stat().st_size))
    return ", ".join(parts)


def size_text(size: float) -> str:
    text = f"{size / 2**30:.1f} ГБ" if size >= 2**30 else f"{size / 2**20:.0f} МБ"
    return text.replace(".", ",")


def status_text(job: dict) -> str:
    status = job["status"]
    if status == "transcribing":
        return f"транскрибация {job.get('progress', 0):.0%}"
    if status == "memo":
        return "мемо, работает Claude"
    if status == "compressing":
        return "сжатие ждёт" if job.get("compress_wait") else f"сжатие {job.get('progress', 0):.0%}"
    if status == "waiting" and job.get("compress") and compression_only(job):
        return "ждёт сжатия"
    if status == "done":
        text = "готово, есть мемо" if job.get("memo_file") else "готово"
        return text + ", сжато" if job.get("compressed") else text
    if status == "error":
        if job.get("compress") and compression_only(job):
            return "сжатие не сделано"
        return "мемо не сделано" if job.get("transcript") else "ошибка"
    return STATUS[status]


def console_python() -> str:
    exe = Path(sys.executable)
    if exe.name.lower() == "pythonw.exe":
        exe = exe.with_name("python.exe")
    return str(exe)


def find_claude() -> str | None:
    appdata = Path(os.environ.get("APPDATA", Path.home()))
    for candidate in (appdata / "npm/node_modules/@anthropic-ai/claude-code/bin/claude.exe",
                      Path.home() / ".local/bin/claude.exe"):
        if candidate.exists():
            return str(candidate)
    return shutil.which("claude")


def flatten(content: object) -> str:
    """Текст результата инструмента: строка или список блоков с полем text."""
    if isinstance(content, list):
        return " ".join(str(item.get("text", "")) for item in content if isinstance(item, dict))
    return str(content or "")


def describe_tool(name: str, data: dict) -> str:
    """Короткое описание текущего шага Claude для живой строки журнала."""
    path = Path(data.get("file_path") or data.get("path") or "").name
    if name == "Read":
        return f"читает {path}"
    if name in ("Edit", "MultiEdit"):
        return f"правит {path}"
    if name in ("Glob", "Grep"):
        return "ищет по файлам проекта"
    if name == "Skill":
        return f"открывает скилл {data.get('skill') or data.get('command') or ''}".strip()
    if name == "Bash":
        return "пробует выполнить команду"
    return f"инструмент {name}"


def thousands(value: float) -> str:
    if value < 1000:
        return str(int(value))
    return f"{value / 1000:.1f}".replace(".", ",") + " тыс."


def claude_stats(result: dict, seconds: float) -> dict:
    """Время, шаги, токены и стоимость по прайсу из итогового события Claude Code."""
    models = (result.get("modelUsage") or {}).values()
    if models:
        fresh = sum(m.get("inputTokens", 0) for m in models)
        cached = sum(m.get("cacheReadInputTokens", 0) for m in models)
        created = sum(m.get("cacheCreationInputTokens", 0) for m in models)
        output = sum(m.get("outputTokens", 0) for m in models)
    else:
        usage = result.get("usage") or {}
        fresh, cached = usage.get("input_tokens", 0), usage.get("cache_read_input_tokens", 0)
        created, output = usage.get("cache_creation_input_tokens", 0), usage.get("output_tokens", 0)
    return {"seconds": seconds, "turns": result.get("num_turns", 0), "input": fresh + cached + created,
            "cached": cached, "output": output, "cost": float(result.get("total_cost_usd") or 0)}


def summary_text(job: dict) -> str:
    parts = []
    if job.get("transcribe_seconds"):
        parts.append(f"транскрибация {minutes(job['transcribe_seconds'])}")
    stats = job.get("claude_stats") or {}
    if stats:
        parts.append(f"мемо {minutes(stats['seconds'])}")
    if job.get("compress_seconds"):
        parts.append(f"сжатие {minutes(job['compress_seconds'])}")
    text = "Итог: " + ", ".join(parts) if parts else "Итог"
    if job.get("compress_result"):
        text += f". Видео: {job['compress_result']}"
    if stats:
        cost = f"{stats['cost']:.2f}".replace(".", ",")
        text += (f". Claude: шагов {stats['turns']}, токенов на входе {thousands(stats['input'])}"
                 f" (из кэша {thousands(stats['cached'])}), на выходе {thousands(stats['output'])},"
                 f" по прайсу ${cost}")
    return text


def journal_entries(job: dict) -> list[tuple[str, str, str]]:
    """Записи журнала как (время, уровень, текст). Старые записи были строками."""
    entries = []
    for entry in job.get("journal", []):
        if isinstance(entry, str):
            stamp, _, text = entry.partition("  ")
            entries.append((stamp, "info", text))
        else:
            entries.append((entry[0], entry[1], entry[2]))
    return entries


def error_hint(message: str) -> str:
    """Понятное объяснение для частых сбоев транскрибации."""
    text = message.lower()
    if "cuda" in text and "out of memory" in text:
        return ("Не хватило памяти видеокарты. Закройте программы, которые её занимают, "
                "или выберите щадящий режим, затем нажмите \"Повторить\".")
    if "failed to allocate memory" in text or "memoryerror" in text or "out of memory" in text:
        return ("Не хватило оперативной памяти: транскрибации нужно 3-4 ГБ. "
                "Закройте лишние программы и нажмите \"Повторить\".")
    return ""


def minutes(seconds: float) -> str:
    return f"{int(seconds) // 60}:{int(seconds) % 60:02}"


def newest_memo(folder: str, since: float) -> Path | None:
    """Файл мемо, записанный после запуска Claude: по скиллу это .xml, без скилла .md."""
    found = [p for pattern in ("*.xml", "*.md") for p in Path(folder).glob(pattern)
             if p.stat().st_mtime >= since - 1]
    return max(found, key=lambda p: p.stat().st_mtime) if found else None


def set_autostart(enabled: bool) -> None:
    OLD_STARTUP_LINK.unlink(missing_ok=True)
    if not enabled:
        STARTUP_LINK.unlink(missing_ok=True)
        return
    subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(INSTALL_SCRIPT),
                    "-Python", console_python(), "-Autostart"],
                   check=True, capture_output=True, creationflags=CREATE_NO_WINDOW)


def windows_dark() -> bool:
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                            r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize") as key:
            return winreg.QueryValueEx(key, "AppsUseLightTheme")[0] == 0
    except OSError:
        return False


def dark_title_bar(window: tk.Misc, dark: bool) -> None:
    """Заголовок окна в цвет темы, как у приложений Windows."""
    try:
        window.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(window.winfo_id())
        value = ctypes.c_int(1 if dark else 0)
        ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 20, ctypes.byref(value), ctypes.sizeof(value))
    except (AttributeError, OSError):
        pass


# столбики звуковой дорожки на мелких размерах: число, ширина и промежуток в пикселях
BAR_LAYOUT = {16: (4, 2, 1), 20: (5, 2, 1), 24: (5, 2, 2), 32: (5, 3, 2), 40: (5, 4, 2), 48: (5, 4, 3)}
BAR_HEIGHTS = {4: (0.5, 1.0, 0.7, 0.85), 5: (0.42, 0.78, 1.0, 0.6, 0.85)}


def draw_icon(size: int, busy: bool = False) -> Image.Image:
    """Значок Memo Maker: скруглённый квадрат с градиентом и столбики звуковой дорожки.

    Каждый размер рисуется отдельно, края столбиков приходятся на границы пикселей,
    поэтому значок остаётся чётким и в трее, и на панели задач.
    """
    top, bottom = BUSY_GRADIENT if busy else IDLE_GRADIENT
    scale = 4
    big = size * scale
    gradient = Image.new("RGBA", (1, big))
    for y in range(big):
        share = y / (big - 1)
        gradient.putpixel((0, y), tuple(round(a + (b - a) * share) for a, b in zip(top, bottom)) + (255,))
    gradient = gradient.resize((big, big))
    mask = Image.new("L", (big, big), 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, big - 1, big - 1), radius=round(size * 0.22) * scale, fill=255)
    image = Image.new("RGBA", (big, big), (0, 0, 0, 0))
    image.paste(gradient, (0, 0), mask)

    count, width, gap = BAR_LAYOUT.get(size) or (5, round(size * 0.085), round(size * 0.055))
    tallest = round(size * (0.62 if size <= 24 else 0.56))
    left = (size - (count * width + (count - 1) * gap)) // 2
    draw = ImageDraw.Draw(image)
    for index, share in enumerate(BAR_HEIGHTS[count]):
        height = max(2, round(tallest * share))
        if (size - height) % 2:
            height += 1
        x = (left + index * (width + gap)) * scale
        y = (size - height) // 2 * scale
        radius = width * scale // 2 if size >= 32 else scale // 2
        draw.rounded_rectangle((x, y, x + width * scale - 1, y + height * scale - 1), radius=radius, fill="white")
    return image.resize((size, size), Image.LANCZOS)


def write_icons() -> None:
    for path, busy in ((ICON, False), (ICON_BUSY, True)):
        frames = [draw_icon(size, busy) for size in ICON_SIZES]
        frames[-1].save(path, format="ICO", sizes=[(size, size) for size in ICON_SIZES],
                        append_images=frames[:-1])


class TrayIcon(pystray.Icon):
    """Значок в трее из готового .ico с нужным размером.

    pystray сам пересохраняет картинку в .ico и при масштабе экрана 125% берёт
    размер 16 вместо 20, отчего значок расплывается. Метод переопределён
    для pystray 0.19.
    """

    ico_path = str(ICON)

    def _assert_icon_handle(self) -> None:
        if self._icon_handle:
            return
        size = ctypes.windll.user32.GetSystemMetrics(49)  # SM_CXSMICON с учётом масштаба экрана
        self._icon_handle = tray_win32.LoadImage(None, self.ico_path, tray_win32.IMAGE_ICON, size, size,
                                                 tray_win32.LR_LOADFROMFILE)


class Store:
    """Настройки и очередь. Общие для окна и рабочего потока, поэтому под замком."""

    def __init__(self) -> None:
        self.lock = threading.RLock()
        self.closed = False
        try:
            data = json.loads(SETTINGS.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            data = {}
        self.watch_dir = Path(data.get("watch_dir", DEFAULT_WATCH))
        self.watch = data.get("watch", True)
        self.out_dirs: list[str] = data.get("out_dirs") or [str(DEFAULT_OUT)]
        self.last_out_dir: str = data.get("last_out_dir") or self.out_dirs[0]
        self.mode: str = data.get("mode", "fast")
        self.memo: bool = data.get("memo", True)
        self.compress: bool = data.get("compress", False)
        self.delete_original: bool = data.get("delete_original", False)
        self.claude_dir: str = data.get("claude_dir", "")
        self.journal_open: bool = data.get("journal_open", True)
        self.jobs: list[dict] = data.get("jobs", [])
        for job in self.jobs:
            if job["status"] in ACTIVE:
                job["status"] = "waiting"
        # при первом запуске старые записи считаются уже разобранными, чтобы не спрашивать о каждой
        if "known" in data:
            self.known = {p for p in data["known"] if Path(p).exists()}
        else:
            self.known = set(list_videos(self.watch_dir))
        self.save()

    def save(self) -> None:
        with self.lock:
            if self.closed:
                return
            data = {
                "watch_dir": str(self.watch_dir),
                "watch": self.watch,
                "out_dirs": self.out_dirs,
                "last_out_dir": self.last_out_dir,
                "mode": self.mode,
                "memo": self.memo,
                "compress": self.compress,
                "delete_original": self.delete_original,
                "claude_dir": self.claude_dir,
                "journal_open": self.journal_open,
                "known": sorted(self.known),
                "jobs": self.jobs,
            }
            SETTINGS_DIR.mkdir(parents=True, exist_ok=True)
            temp = SETTINGS.with_suffix(".tmp")
            temp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            os.replace(temp, SETTINGS)


class Worker(threading.Thread):
    """Обрабатывает очередь по одной встрече: транскрибация, затем мемо, затем сжатие видео."""

    def __init__(self, app: App) -> None:
        super().__init__(daemon=True)
        self.app = app
        self.store = app.store
        self.wake = threading.Event()
        self.proc: subprocess.Popen | None = None
        self.current: dict | None = None
        self.cancelled = False

    def run(self) -> None:
        while True:
            job = self.next_job()
            if job is None:
                self.wake.wait(5)
                self.wake.clear()
                continue
            self.current, self.cancelled = job, False
            try:
                self.process(job)
            except Exception as error:  # один сбой не должен останавливать очередь
                self.update(job, status="error", note=f"сбой: {error}")
            finally:
                self.current, self.proc = None, None

    def next_job(self) -> dict | None:
        """Первая ждущая встреча. Встречи, которым осталось только сжатие, пропускают вперёд остальные."""
        with self.store.lock:
            waiting = [job for job in self.store.jobs if job["status"] == "waiting"]
            return next((job for job in waiting if not compression_only(job)), waiting[0] if waiting else None)

    def update(self, job: dict, save: bool = True, **fields: object) -> None:
        with self.store.lock:
            job.update(fields)
            if save:
                self.store.save()
        self.app.post("refresh")

    def log(self, job: dict, text: str, level: str = "info", live: bool = False) -> None:
        """Запись в журнал хода работы встречи.

        Уровень задаёт выделение: stage для ключевых этапов, error, reply для ответа
        Claude, summary для итога. Живая строка показывает текущий прогресс и заменяется
        следующей записью, поэтому прогресс и шаги Claude занимают в журнале одну строку.
        Журнал сохраняется на диск вместе с ближайшей сменой статуса.
        """
        entry = [f"{datetime.now():%H:%M:%S}", level, text]
        with self.store.lock:
            journal = job.setdefault("journal", [])
            if journal and job.get("journal_live"):
                journal[-1] = entry
            else:
                journal.append(entry)
            job["journal_live"] = live
            del journal[:-JOURNAL_LINES]
        self.app.post("refresh")

    def cancel(self) -> None:
        self.cancelled = True
        if self.proc and self.proc.poll() is None:
            self.proc.kill()

    def process(self, job: dict) -> None:
        name = job["name"]
        if not has_file(job, "transcript"):
            # если оригинал удалён после сжатия, транскрипция делается заново по сжатому файлу
            source = next((Path(job[key]) for key in ("video", "compressed") if has_file(job, key)), None)
            if source is None:
                self.log(job, f"Нет файла записи: {job['video']}", "error")
                self.update(job, status="error", note=f"нет файла: {job['video']}")
                return
            self.update(job, status="transcribing", progress=0.0, note="")
            started = time.time()
            transcript = self.transcribe(job, source)
            if self.cancelled:
                self.log(job, "Транскрибация прервана", "error")
                self.update(job, status="cancelled")
                return
            if transcript is None:
                hint = error_hint(job["note"])
                if hint:
                    job["note"] = f"{hint}\n\n{job['note']}"
                self.log(job, f"Транскрибация не удалась. {job['note']}", "error")
                self.update(job, status="error")
                self.app.post("notify", "Ошибка транскрибации", name)
                return
            job["transcribe_seconds"] = time.time() - started
            self.log(job, f"Транскрипция готова за {minutes(job['transcribe_seconds'])}: {transcript.name}", "stage")
            self.update(job, transcript=str(transcript))
            self.app.post("notify", "Транскрибация готова", name)
        if job["memo"] and not has_file(job, "memo_file"):
            self.update(job, status="memo", claude_stats={})
            done = self.make_memo(job)
            if self.cancelled:
                self.log(job, "Мемо прервано", "error")
                self.update(job, status="cancelled")
                return
            if not done:
                self.log(job, f"Мемо не сделано. {job['note'][:300]}", "error")
                self.log(job, summary_text(job), "summary")
                self.update(job, status="error")
                self.app.post("notify", "Мемо не сделано", f"{name}. {job['note'][:120]}")
                return
            self.app.post("notify", "Мемо готово", name)
        if compression_pending(job):
            outcome = self.compress(job)
            self.update(job, save=False, compress_wait="")
            if self.cancelled:
                self.log(job, "Сжатие прервано, оригинал не тронут", "error")
                self.update(job, status="cancelled")
                return
            if outcome == QUEUE:
                self.log(job, "Сжатие подождёт: сначала транскрибация других встреч из очереди", "stage")
                self.update(job, status="waiting", progress=0.0)
                return
            if outcome is None:
                self.log(job, f"Сжатие не удалось, оригинал не тронут. {job['note']}", "error")
                self.update(job, status="error")
                self.app.post("notify", "Сжатие не удалось", name)
                return
        self.log(job, summary_text(job), "summary")
        self.update(job, status="done")

    def transcribe(self, job: dict, source: Path) -> Path | None:
        target = Path(job["out_dir"]) / f"{job['name']}.txt"
        cmd = [console_python(), "-u", str(TRANSCRIBE), str(source), "--name", job["name"],
               "--out", job["out_dir"], "--mode", job["mode"]]
        env = dict(os.environ, PYTHONIOENCODING="utf-8")
        log: list[str] = []
        self.log(job, f"Транскрибация началась, режим \"{MODES[job['mode']]}\"", "stage")
        self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                     encoding="utf-8", errors="replace", env=env, cwd=APP_DIR,
                                     creationflags=CREATE_NO_WINDOW)
        if self.cancelled:
            self.proc.kill()
        for line in self.proc.stdout:
            line = line.strip()
            match = PROGRESS.match(line)
            if match:
                self.update(job, save=False, progress=float(match.group(1)) / 100)
                self.log(job, f"Распознано {line}", live=True)
            elif line:
                log.append(line)
                if not line.startswith(job["out_dir"]):
                    self.log(job, line, live=True)
        code = self.proc.wait()
        with self.store.lock:
            job["log"] = log[-40:]
            if code == 0 and target.exists():
                return target
            job["note"] = log[-1] if log else f"код возврата {code}"
        return None

    def make_memo(self, job: dict) -> bool:
        exe = find_claude()
        if not exe:
            job["note"] = "Claude Code не найден."
            return False
        folder = job["out_dir"]
        # Claude работает в папке проекта, чтобы видеть его скилл и правила; без проекта в папке с результатом
        project = self.store.claude_dir if self.store.claude_dir and Path(self.store.claude_dir).is_dir() else folder
        prompt = MEMO_PROMPT.format(transcript=job["transcript"], folder=folder)
        # stream-json отдаёт ход работы по событиям: вызовы инструментов, реплики, итог
        cmd = [exe, "-p", "--output-format", "stream-json", "--verbose", "--permission-mode", "acceptEdits",
               "--add-dir", folder, "--allowedTools", CLAUDE_TOOLS]
        started = time.time()
        self.log(job, f"Мемо: запущен Claude Code в {project}", "stage")

        def activity(text: str) -> None:
            self.log(job, f"Claude работает {minutes(time.time() - started)}: {text}", live=True)

        self.proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                                     errors="replace", cwd=project, creationflags=CREATE_NO_WINDOW)
        if self.cancelled:
            self.proc.kill()
        timed_out = threading.Event()

        def stop_on_timeout() -> None:
            timed_out.set()
            self.proc.kill()

        timer = threading.Timer(MEMO_TIMEOUT, stop_on_timeout)
        timer.start()
        try:
            self.proc.stdin.write(prompt)
            self.proc.stdin.close()
        except OSError:
            pass
        raw: list[str] = []
        result: dict | None = None
        last_activity = 0.0
        for line in self.proc.stdout:
            line = line.strip()
            if not line:
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                raw.append(line)
                activity(line[:200])
                continue
            kind, subtype = event.get("type"), event.get("subtype")
            if kind == "system" and subtype == "init":
                activity(f"модель {event.get('model', 'не указана')}")
            elif kind == "system" and subtype == "thinking_tokens":
                # событий о размышлениях много, строку достаточно обновлять раз в секунду
                if time.time() - last_activity >= 1:
                    last_activity = time.time()
                    activity("думает")
            elif kind == "assistant":
                for item in event.get("message", {}).get("content", []):
                    if item.get("type") == "tool_use" and item.get("name") == "Write":
                        written = Path((item.get("input") or {}).get("file_path", "")).name
                        self.log(job, f"Мемо записано: {written}", "stage")
                    elif item.get("type") == "tool_use":
                        activity(describe_tool(item.get("name", ""), item.get("input") or {}))
                    elif item.get("type") == "text" and item.get("text", "").strip():
                        activity(item["text"].strip().splitlines()[0][:150])
            elif kind == "user":
                content = event.get("message", {}).get("content", [])
                for item in content if isinstance(content, list) else []:
                    if isinstance(item, dict) and item.get("type") == "tool_result" and item.get("is_error"):
                        activity("инструмент вернул ошибку: " + flatten(item.get("content"))[:150])
            elif kind == "result":
                result = event
        self.proc.wait()
        timer.cancel()

        memo = newest_memo(folder, started)
        reply = str(result.get("result") or "") if result else "\n".join(raw[-20:])
        failed = result is None or bool(result.get("is_error"))
        with self.store.lock:
            job["note"] = reply
            job["memo_file"] = str(memo) if memo else ""
            if result:
                job["claude_stats"] = claude_stats(result, time.time() - started)
            if any("Not logged in" in line for line in raw):
                job["note"] = LOGIN_HINT
            elif timed_out.is_set():
                job["note"] = "Claude не уложился в 30 минут."
            elif not failed and memo is None:
                job["note"] = "Claude ответил, но файл мемо не появился.\n\n" + reply
        done = not failed and memo is not None and not timed_out.is_set()
        if done:
            self.log(job, "Ответ Claude:\n" + reply.strip(), "reply")
        return done

    # --- сжатие видео ---

    def compress(self, job: dict) -> str | None:
        """Сжимает запись в H.265 рядом с оригиналом и по желанию удаляет оригинал.

        Возвращает "done", в том числе когда сжимать нечего (причина в журнале), QUEUE, если сжатие
        уступило очередь другой встрече, и None при ошибке, текст ошибки в job["note"].
        """
        video = Path(job["video"])
        ffmpeg, ffprobe = shutil.which("ffmpeg"), shutil.which("ffprobe")
        if not video.exists():
            return self.skip_compression(job, f"нет файла записи {video}")
        if not (ffmpeg and ffprobe):
            job["note"] = "Не найден ffmpeg: установите его и добавьте папку с ffmpeg.exe в PATH."
            return None
        info = probe_media(ffprobe, video)
        if info is None:
            job["note"] = f"ffprobe не смог прочитать {video.name}"
            return None
        if not info["codec"]:
            return self.skip_compression(job, "в файле нет видео")
        if info["codec"] in MODERN_CODECS:
            return self.skip_compression(job, f"видео {MODERN_CODECS[info['codec']]}")

        target = compressed_path(video)
        existing = probe_media(ffprobe, target) if target.exists() else None
        if existing and existing["codec"] == "hevc" and same_duration(existing, info["duration"]):
            self.log(job, f"Сжатая копия уже есть: {target.name}", "stage")
        else:
            outcome = self.encode(job, ffmpeg, video, target, info)
            if outcome != "done":
                return outcome
            if not same_duration(probe_media(ffprobe, target), info["duration"]):
                target.unlink(missing_ok=True)
                job["note"] = "у сжатого файла другая длительность, он удалён"
                return None

        original_size, new_size = video.stat().st_size, target.stat().st_size
        share = new_size / original_size
        if share > 1 - MIN_SAVING:
            target.unlink(missing_ok=True)
            return self.skip_compression(job, f"не выгодно, сжатый файл {share:.0%} от оригинала")
        result = f"{size_text(original_size)} → {size_text(new_size)} ({share:.0%})"
        if job.get("delete_original"):
            # полное декодирование дольше быстрой проверки, поэтому только когда оригинал будет удалён
            self.log(job, "Проверка сжатого файла перед удалением оригинала: декодирование целиком", live=True)
            problem = self.verify(ffmpeg, target)
            if self.cancelled:
                return None
            if problem:
                target.unlink(missing_ok=True)
                job["note"] = problem
                return None
            try:
                video.unlink()
                result += ", оригинал удалён"
            except OSError as error:
                result += f", оригинал удалить не удалось: {error}"
        with self.store.lock:
            job["compressed"], job["compress_result"] = str(target), result
        self.log(job, f"Видео сжато: {result}. Файл {target}", "stage")
        self.app.post("notify", "Сжатие готово", f"{job['name']}: {result}")
        return "done"

    def encode(self, job: dict, ffmpeg: str, video: Path, target: Path, info: dict) -> str | None:
        """Запускает ffmpeg, пока видеокарта никому не нужна. Результат пишется в .part и появляется готовым."""
        partial = target.with_name(target.name + ".part")
        cmd = compress_cmd(ffmpeg, video, partial, info)
        total_us = info["duration"] * 1_000_000
        while True:
            self.update(job, status="compressing", progress=0.0)
            reason = self.wait_for_gpu(job)
            if reason == QUEUE or self.cancelled:
                return reason
            self.log(job, f"Сжатие в H.265 началось: {video.name}, {size_text(video.stat().st_size)}", "stage")
            started = checked = time.time()
            log: list[str] = []
            speed, stopped = "", None
            self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                         encoding="utf-8", errors="replace",
                                         creationflags=CREATE_NO_WINDOW | BELOW_NORMAL_PRIORITY_CLASS)
            if self.cancelled:
                self.proc.kill()
            for line in self.proc.stdout:
                line = line.strip()
                if match := FFMPEG_SPEED.match(line):
                    speed = f", скорость {float(match.group(1)):.1f}×".replace(".", ",")
                elif match := FFMPEG_TIME.match(line):
                    progress = min(int(match.group(1)) / total_us, 1.0) if total_us else 0.0
                    self.update(job, save=False, progress=progress)
                    self.log(job, f"Сжато {progress:.0%}{speed}", live=True)
                elif line and not FFMPEG_KEY.match(line):
                    log.append(line)
                # видеокарта понадобилась записи или транскрибации: сжатие остановится и потом начнётся заново
                if stopped is None and time.time() - checked >= COMPRESS_CHECK_SECONDS:
                    checked = time.time()
                    stopped = self.compress_blocker(job)
                    if stopped:
                        self.proc.kill()
            code = self.proc.wait()
            if self.cancelled or stopped:
                partial.unlink(missing_ok=True)
                if self.cancelled:
                    return None
                self.log(job, f"Сжатие остановлено, потом начнётся заново: {stopped}", "stage")
                continue
            if code != 0 or not partial.exists():
                partial.unlink(missing_ok=True)
                job["note"] = log[-1] if log else f"ffmpeg завершился с кодом {code}"
                return None
            stat = video.stat()
            os.replace(partial, target)
            os.utime(target, (stat.st_atime, stat.st_mtime))  # дата как у записи, проводник сортирует по ней
            job["compress_seconds"] = time.time() - started
            return "done"

    def compress_blocker(self, job: dict) -> str | None:
        """Почему сжатию сейчас лучше не занимать видеокарту, или None."""
        with self.store.lock:
            if any(other is not job and other["status"] == "waiting" and not compression_only(other)
                   for other in self.store.jobs):
                return QUEUE
        if self.app.recording():
            return "OBS пишет новую запись"
        if self.app.dialog is not None:
            return "открыто окно новой записи"
        return None

    def wait_for_gpu(self, job: dict) -> str | None:
        """Ждёт, пока закончится запись и закроется окно новой записи.

        Возвращает QUEUE, если сжатие должно уступить очередь, и None, когда можно сжимать
        или сжатие отменили.
        """
        while not self.cancelled:
            reason = self.compress_blocker(job)
            if reason is None or reason == QUEUE:
                self.update(job, save=False, compress_wait="")
                return reason
            if job.get("compress_wait") != reason:
                self.update(job, save=False, compress_wait=reason)
                self.log(job, f"Сжатие ждёт: {reason}")
            time.sleep(COMPRESS_CHECK_SECONDS)
        return None

    def verify(self, ffmpeg: str, path: Path) -> str | None:
        """Ошибки полного декодирования сжатого файла или None."""
        self.proc = subprocess.Popen([ffmpeg, "-hide_banner", "-nostdin", "-v", "error", "-hwaccel", "cuda",
                                      "-i", str(path), "-f", "null", "-"],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
                                     encoding="utf-8", errors="replace",
                                     creationflags=CREATE_NO_WINDOW | BELOW_NORMAL_PRIORITY_CLASS)
        _, stderr = self.proc.communicate()
        # предупреждения о метках времени у записей с переменной частотой кадров файл не портят
        errors = [line for line in stderr.splitlines()
                  if line.strip() and "non monotonically increasing dts" not in line
                  and not line.startswith("[null @") and "Last message repeated" not in line]
        if self.proc.returncode or errors:
            return "сжатый файл декодируется с ошибками: " + (" ".join(errors)[-200:] or f"код {self.proc.returncode}")
        return None

    def skip_compression(self, job: dict, reason: str) -> str:
        with self.store.lock:
            job["compress_skip"], job["compress_result"] = reason, f"не сжато, {reason}"
        self.log(job, f"Сжатие пропущено: {reason}", "stage")
        return "done"


class App:
    def __init__(self, hidden: bool) -> None:
        self.store = Store()
        self.events: queue.Queue = queue.Queue()
        self.candidates: dict[str, tuple[tuple[int, float], float]] = {}
        self.asked: set[str] = set()
        self.prompts: deque[Path] = deque()
        self.dialog: tk.Toplevel | None = None
        self.tray_busy: bool | None = None

        self.journal_shown: tuple | None = None
        self.images: dict[str, ImageTk.PhotoImage] = {}
        self.dark = windows_dark()
        if OLD_STARTUP_LINK.exists():
            try:
                set_autostart(True)
            except (OSError, subprocess.CalledProcessError):
                pass

        self.root = tk.Tk()
        self.root.withdraw()
        self.root.title(TITLE)
        self.root.geometry("1120x760")
        self.root.minsize(1000, 460)
        self.root.protocol("WM_DELETE_WINDOW", self.root.withdraw)
        sv_ttk.set_theme("dark" if self.dark else "light")
        self.root.iconbitmap(default=str(ICON))
        self.scale = self.root.winfo_fpixels("1i") / 96
        self.muted = "#9a9a9a" if self.dark else "#5f5f5f"
        self.icons = {False: draw_icon(64), True: draw_icon(64, busy=True)}
        self.build()
        dark_title_bar(self.root, self.dark)
        if not hidden:
            self.root.deiconify()

        self.worker = Worker(self)
        self.worker.start()
        self.tray = TrayIcon("MemoMaker", self.icons[False], TITLE, self.tray_menu())
        threading.Thread(target=self.tray.run, daemon=True).start()
        self.refresh()
        self.root.after(200, self.pump)
        self.root.after(1000, self.scan)

    # --- окно ---

    def icon(self, name: str, on_accent: bool = False) -> ImageTk.PhotoImage:
        """Значок для кнопки из шрифта Segoe Fluent Icons в цвет текста кнопки."""
        key = f"{name}:{on_accent}"
        if key not in self.images:
            size = round(16 * self.scale)
            if on_accent:
                color = "#000000" if self.dark else "#ffffff"
            else:
                color = "#ffffff" if self.dark else "#1a1a1a"
            image = Image.new("RGBA", (size, size), (0, 0, 0, 0))
            try:
                font = ImageFont.truetype(str(ICON_FONT), size)
                ImageDraw.Draw(image).text((size / 2, size / 2), GLYPHS[name], font=font, fill=color, anchor="mm")
            except OSError:
                pass  # без шрифта значков кнопка остаётся с одной подписью
            self.images[key] = ImageTk.PhotoImage(image)
        return self.images[key]

    def button(self, parent: tk.Misc, text: str, icon: str, command, accent: bool = False) -> ttk.Button:
        return ttk.Button(parent, text=" " + text, image=self.icon(icon, accent), compound="left",
                          command=command, style="Accent.TButton" if accent else "TButton")

    def build(self) -> None:
        frame = self.frame = ttk.Frame(self.root, padding=(14, 12))
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(0, weight=1)
        frame.rowconfigure(1, weight=2)
        frame.rowconfigure(4, weight=3)

        toolbar = ttk.Frame(frame)
        toolbar.grid(row=0, column=0, columnspan=2, sticky="we", pady=(0, 10))
        self.button(toolbar, "Добавить запись…", "add", self.add_file, accent=True).pack(side="left")
        self.button(toolbar, "Очистить готовые", "clear", self.clear_finished).pack(side="right")

        columns = (("name", "Встреча", 340, True), ("mode", "Режим", 80, False),
                   ("status", "Статус", 190, False), ("folder", "Папка", 200, True))
        self.tree = ttk.Treeview(frame, columns=[c[0] for c in columns], show="headings", selectmode="browse",
                                 height=5)
        for key, text, width, stretch in columns:
            self.tree.heading(key, text=text, anchor="w")
            self.tree.column(key, width=width, anchor="w", stretch=stretch)
        scroll = ttk.Scrollbar(frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=scroll.set)
        self.tree.grid(row=1, column=0, sticky="nsew")
        scroll.grid(row=1, column=1, sticky="ns")
        self.tree.bind("<Double-1>", lambda event: self.open_result())
        self.tree.bind("<Button-3>", self.context_menu)
        self.tree.bind("<<TreeviewSelect>>", lambda event: self.show_journal())

        actions = (("Выше", "up", self.move_up), ("Сменить режим", "mode", self.toggle_mode),
                   ("Повторить", "retry", self.retry), ("Убрать", "remove", self.remove),
                   ("Подробнее", "details", self.details))
        opens = (("Транскрипция", "transcript", lambda: self.open_job_file("transcript")),
                 ("Мемо", "memo", lambda: self.open_job_file("memo_file")))
        buttons = ttk.Frame(frame)
        buttons.grid(row=2, column=0, columnspan=2, sticky="w", pady=(10, 0))
        for text, icon, command in actions:
            self.button(buttons, text, icon, command).pack(side="left", padx=(0, 6))
        for index, (text, icon, command) in enumerate(opens):
            self.button(buttons, text, icon, command).pack(side="left", padx=(12 if index == 0 else 0, 6))

        menu_colors = {"background": "#2b2b2b", "foreground": "#ffffff", "activebackground": "#3d3d3d",
                       "activeforeground": "#ffffff"} if self.dark else {}
        self.menu = tk.Menu(self.root, tearoff=False, relief="flat", borderwidth=0, **menu_colors)
        for text, icon, command in actions:
            self.menu.add_command(label=text, command=command)
        self.menu.add_separator()
        self.menu.add_command(label="Открыть транскрипцию", command=opens[0][2])
        self.menu.add_command(label="Открыть мемо", command=opens[1][2])
        self.menu.add_command(label="Открыть папку", command=self.open_folder)

        self.journal_toggle = ttk.Button(frame, text=" Ход работы", compound="left", style="Toolbutton",
                                         command=self.toggle_journal)
        self.journal_toggle.grid(row=3, column=0, sticky="w", pady=(12, 0))
        self.journal_body = ttk.Frame(frame)
        self.journal_body.grid(row=4, column=0, columnspan=2, sticky="nsew", pady=(4, 0))
        self.journal_body.columnconfigure(0, weight=1)
        self.journal_body.rowconfigure(0, weight=1)
        mono = ("Cascadia Mono", 9)
        self.journal = tk.Text(self.journal_body, height=8, wrap="word", font=mono,
                               background="#141414", foreground="#d4d4d4", insertbackground="#d4d4d4",
                               borderwidth=0, highlightthickness=0, padx=10, pady=8, state="disabled")
        self.journal.tag_configure("time", foreground="#6f6f6f")
        self.journal.tag_configure("info", foreground="#9d9d9d")
        self.journal.tag_configure("stage", foreground="#4fc1ff", font=(*mono, "bold"))
        self.journal.tag_configure("error", foreground="#f48771", font=(*mono, "bold"))
        self.journal.tag_configure("reply", foreground="#d4d4d4")
        self.journal.tag_configure("summary", foreground="#dcdcaa", font=(*mono, "bold"))
        journal_scroll = ttk.Scrollbar(self.journal_body, orient="vertical", command=self.journal.yview)
        self.journal.configure(yscrollcommand=journal_scroll.set)
        self.journal.grid(row=0, column=0, sticky="nsew")
        journal_scroll.grid(row=0, column=1, sticky="ns")
        self.apply_journal_state()

        settings = ttk.Frame(frame)
        settings.grid(row=5, column=0, columnspan=2, sticky="we", pady=(12, 0))
        settings.columnconfigure(1, weight=1)
        self.watch_var = tk.BooleanVar(value=self.store.watch)
        ttk.Checkbutton(settings, text="Следить за папкой", variable=self.watch_var, style="Switch.TCheckbutton",
                        command=self.on_watch_toggle).grid(row=0, column=0, sticky="w")
        self.watch_label = ttk.Label(settings, text=str(self.store.watch_dir))
        self.watch_label.grid(row=0, column=1, sticky="w", padx=10)
        self.button(settings, "Изменить…", "folder", self.change_watch_dir).grid(row=0, column=2, sticky="e")

        ttk.Label(settings, text="Сохранять в").grid(row=1, column=0, sticky="w", pady=(8, 0))
        self.out_var = tk.StringVar(value=self.store.last_out_dir)
        self.out_combo = ttk.Combobox(settings, textvariable=self.out_var, values=self.store.out_dirs,
                                      state="readonly")
        self.out_combo.grid(row=1, column=1, sticky="we", padx=10, pady=(8, 0))
        self.out_combo.bind("<<ComboboxSelected>>", lambda event: self.set_out_dir(self.out_var.get()))
        out_buttons = ttk.Frame(settings)
        out_buttons.grid(row=1, column=2, sticky="e", pady=(8, 0))
        self.button(out_buttons, "Добавить…", "new_folder", lambda: self.add_out_dir(self.root)).pack(side="left")
        self.button(out_buttons, "Убрать из списка", "minus",
                    lambda: self.drop_out_dir(self.out_var.get())).pack(side="left", padx=(6, 0))

        ttk.Label(settings, text="Проект для мемо").grid(row=2, column=0, sticky="w", pady=(8, 0))
        self.claude_label = ttk.Label(settings)
        self.claude_label.grid(row=2, column=1, sticky="w", padx=10, pady=(8, 0))
        self.button(settings, "Изменить…", "folder", self.change_claude_dir).grid(
            row=2, column=2, sticky="e", pady=(8, 0))
        self.show_claude_dir()

        self.startup_var = tk.BooleanVar(value=STARTUP_LINK.exists())
        ttk.Checkbutton(settings, text="Запускать вместе с Windows", variable=self.startup_var,
                        style="Switch.TCheckbutton", command=self.on_startup_toggle).grid(
            row=3, column=0, columnspan=2, sticky="w", pady=(10, 0))

        self.status = ttk.Label(frame, foreground=self.muted)
        self.status.grid(row=6, column=0, columnspan=2, sticky="w", pady=(10, 0))

    def show_claude_dir(self) -> None:
        text = self.store.claude_dir or "не задан: Claude работает в папке с результатом, без скилла проекта"
        self.claude_label.config(text=text, foreground="" if self.store.claude_dir else self.muted)

    def change_claude_dir(self) -> None:
        """Папка, в которой запускается Claude Code: там лежат скилл meeting-memo и правила проекта."""
        chosen = filedialog.askdirectory(parent=self.root, title="Проект Claude для мемо",
                                         initialdir=self.store.claude_dir or str(Path.home()))
        if not chosen:
            return
        with self.store.lock:
            self.store.claude_dir = str(Path(chosen))
            self.store.save()
        self.show_claude_dir()

    def toggle_journal(self) -> None:
        with self.store.lock:
            self.store.journal_open = not self.store.journal_open
            self.store.save()
        self.apply_journal_state()

    def apply_journal_state(self) -> None:
        """Журнал свёрнут или развёрнут. Свёрнутый отдаёт место списку встреч."""
        if self.store.journal_open:
            self.journal_body.grid()
            self.frame.rowconfigure(4, weight=3)
        else:
            self.journal_body.grid_remove()
            self.frame.rowconfigure(4, weight=0)
        self.journal_toggle.config(image=self.icon("expanded" if self.store.journal_open else "collapsed"))

    def refresh(self) -> None:
        with self.store.lock:
            jobs = [dict(job) for job in self.store.jobs]
            watch = self.store.watch
        ids = [job["id"] for job in jobs]
        for item in self.tree.get_children():
            if item not in ids:
                self.tree.delete(item)
        for index, job in enumerate(jobs):
            values = (job["name"], MODES[job["mode"]], status_text(job), Path(job["out_dir"]).name)
            if self.tree.exists(job["id"]):
                self.tree.item(job["id"], values=values)
                self.tree.move(job["id"], "", index)
            else:
                self.tree.insert("", index, iid=job["id"], values=values)

        busy = next((job for job in jobs if job["status"] in ACTIVE), None)
        if jobs and not self.tree.selection():
            self.tree.selection_set((busy or jobs[-1])["id"])
        self.show_journal()
        waiting = sum(job["status"] == "waiting" for job in jobs)
        tip = f"{busy['name']}: {status_text(busy)}" if busy else "Сейчас ничего не обрабатывается"
        if waiting:
            tip += f", в очереди ещё {waiting}"
        self.status.config(text=tip if watch else f"{tip}. Слежение за папкой выключено.")
        self.tray.title = f"{TITLE}\n{tip}"[:120]
        if self.tray_busy != bool(busy):
            self.tray_busy = bool(busy)
            self.tray.ico_path = str(ICON_BUSY if busy else ICON)
            self.tray.icon = self.icons[self.tray_busy]

    def selected(self) -> dict | None:
        selection = self.tree.selection()
        if not selection:
            return None
        with self.store.lock:
            return next((job for job in self.store.jobs if job["id"] == selection[0]), None)

    def show_journal(self) -> None:
        """Показывает журнал выбранной встречи, перерисовывает только при изменениях."""
        job = self.selected()
        with self.store.lock:
            entries = journal_entries(job) if job else []
        key = (job["id"], len(entries), entries[-1] if entries else None) if job else None
        if key == self.journal_shown:
            return
        self.journal_shown = key
        self.journal_toggle.config(text=f" Ход работы: {job['name']}" if job else " Ход работы")
        at_end = self.journal.yview()[1] >= 0.999
        self.journal.config(state="normal")
        self.journal.delete("1.0", "end")
        if not entries:
            self.journal.insert("end", "Записей пока нет.", "info")
        for index, (stamp, level, text) in enumerate(entries):
            if index:
                self.journal.insert("end", "\n")
            self.journal.insert("end", stamp + "  ", "time")
            self.journal.insert("end", text.replace("\n", "\n" + " " * (len(stamp) + 2)), level)
        self.journal.config(state="disabled")
        if at_end:
            self.journal.see("end")

    # --- папки для результатов ---

    def sync_out_dirs(self) -> None:
        self.out_combo["values"] = self.store.out_dirs
        self.out_var.set(self.store.last_out_dir)

    def set_out_dir(self, path: str) -> None:
        with self.store.lock:
            self.store.last_out_dir = path
            self.store.save()

    def add_out_dir(self, parent: tk.Misc) -> str | None:
        chosen = filedialog.askdirectory(parent=parent, initialdir=self.store.last_out_dir or str(Path.home()))
        if not chosen:
            return None
        chosen = str(Path(chosen))
        with self.store.lock:
            if chosen not in self.store.out_dirs:
                self.store.out_dirs.append(chosen)
            self.store.last_out_dir = chosen
            self.store.save()
        self.sync_out_dirs()
        return chosen

    def drop_out_dir(self, path: str) -> None:
        """Убирает папку только из списка, сама папка и файлы в ней не трогаются."""
        with self.store.lock:
            if len(self.store.out_dirs) < 2 or path not in self.store.out_dirs:
                return
            self.store.out_dirs.remove(path)
            if self.store.last_out_dir == path:
                self.store.last_out_dir = self.store.out_dirs[0]
            self.store.save()
        self.sync_out_dirs()

    def show(self) -> None:
        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()

    # --- связь с треем и рабочим потоком ---

    def post(self, *event: object) -> None:
        self.events.put(event)

    def pump(self) -> None:
        refresh = False
        try:
            while True:
                kind, *args = self.events.get_nowait()
                if kind == "refresh":
                    refresh = True
                elif kind == "notify":
                    self.notify(*args)
                elif kind == "show":
                    self.show()
                elif kind == "add":
                    self.add_file()
                elif kind == "watch":
                    self.watch_var.set(not self.watch_var.get())
                    self.on_watch_toggle()
                elif kind == "quit":
                    self.quit()
                    return
        except queue.Empty:
            pass
        if refresh:
            self.refresh()
        self.root.after(200, self.pump)

    def notify(self, title: str, message: str) -> None:
        try:
            self.tray.notify(message or " ", title)
        except Exception:  # уведомление вспомогательное, очередь от него не зависит
            pass

    def tray_menu(self) -> pystray.Menu:
        return pystray.Menu(
            pystray.MenuItem("Открыть", lambda icon, item: self.post("show"), default=True),
            pystray.MenuItem("Добавить запись…", lambda icon, item: self.post("add")),
            pystray.MenuItem("Следить за папкой", lambda icon, item: self.post("watch"),
                             checked=lambda item: self.store.watch),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem("Выход", lambda icon, item: self.post("quit")),
        )

    def quit(self) -> None:
        if self.worker.current and not messagebox.askyesno(
                TITLE, "Идёт обработка встречи. Выйти? Она продолжится при следующем запуске."):
            self.root.after(200, self.pump)
            return
        with self.store.lock:
            for job in self.store.jobs:
                if job["status"] in ACTIVE:
                    job["status"] = "waiting"
            self.store.save()
            self.store.closed = True
        if self.worker.proc and self.worker.proc.poll() is None:
            self.worker.proc.kill()
        self.tray.stop()
        self.root.destroy()

    # --- слежение за папкой ---

    def scan(self) -> None:
        try:
            if self.store.watch:
                self.check_folder()
        finally:
            self.root.after(SCAN_MS, self.scan)

    def recording(self) -> bool:
        """OBS пишет новую запись: в папке наблюдения есть новый файл, который ещё растёт или открыт."""
        return self.store.watch and bool(self.candidates)

    def check_folder(self) -> None:
        """Запись считается законченной, когда файл не растёт и его никто не держит открытым."""
        now = time.time()
        videos = list_videos(self.store.watch_dir)
        # пропавший файл не должен навсегда считаться идущей записью, иначе сжатие будет ждать вечно
        for path in set(self.candidates) - set(videos):
            del self.candidates[path]
        for path in videos:
            if path in self.store.known or path in self.asked:
                continue
            try:
                stat = os.stat(path)
            except OSError:
                continue
            signature = (stat.st_size, stat.st_mtime)
            seen = self.candidates.get(path)
            if seen is None or seen[0] != signature:
                self.candidates[path] = (signature, now)
                continue
            if now - seen[1] < STABLE_SECONDS or is_busy(Path(path)):
                continue
            del self.candidates[path]
            self.asked.add(path)
            self.notify("Запись закончена", Path(path).name)
            self.ask(Path(path))

    # --- окно с вопросом о новой записи ---

    def ask(self, video: Path) -> None:
        if self.dialog is not None:
            self.prompts.append(video)
            return
        dialog = self.dialog = tk.Toplevel(self.root)
        dialog.withdraw()
        dialog.title(f"{TITLE}: новая запись")
        dialog.resizable(False, False)
        dialog.attributes("-topmost", True)
        body = ttk.Frame(dialog, padding=(18, 16))
        body.pack(fill="both", expand=True)

        ttk.Label(body, text=video.name, font="SunValleyBodyStrongFont").grid(
            row=0, column=0, columnspan=3, sticky="w")
        ttk.Label(body, text=describe(video), foreground=self.muted).grid(
            row=1, column=0, columnspan=3, sticky="w", pady=(2, 14))

        ttk.Label(body, text="Название").grid(row=2, column=0, sticky="w", padx=(0, 12))
        name = tk.StringVar(value=default_name(video))
        entry = ttk.Entry(body, textvariable=name, width=60)
        entry.grid(row=2, column=1, columnspan=2, sticky="we", pady=4)

        ttk.Label(body, text="Сохранить в").grid(row=3, column=0, sticky="w", padx=(0, 12))
        folder = tk.StringVar(value=self.store.last_out_dir)
        combo = ttk.Combobox(body, textvariable=folder, values=self.store.out_dirs, state="readonly", width=50)
        combo.grid(row=3, column=1, sticky="we", pady=4)

        def add_folder() -> None:
            if self.add_out_dir(dialog):
                combo["values"] = self.store.out_dirs
                folder.set(self.store.last_out_dir)

        def drop_folder() -> None:
            self.drop_out_dir(folder.get())
            combo["values"] = self.store.out_dirs
            folder.set(self.store.last_out_dir)

        folder_buttons = ttk.Frame(body)
        folder_buttons.grid(row=3, column=2, sticky="w")
        self.button(folder_buttons, "Добавить…", "new_folder", add_folder).pack(side="left", padx=(6, 0))
        self.button(folder_buttons, "Убрать из списка", "minus", drop_folder).pack(side="left", padx=(6, 0))

        ttk.Label(body, text="Режим").grid(row=4, column=0, sticky="nw", padx=(0, 12), pady=(10, 0))
        mode = tk.StringVar(value=self.store.mode)
        modes = ttk.Frame(body)
        modes.grid(row=4, column=1, columnspan=2, sticky="w", pady=(10, 0))
        ttk.Radiobutton(modes, text="Быстро: вся мощность видеокарты", variable=mode, value="fast").pack(anchor="w")
        ttk.Radiobutton(modes, text="Щадяще: дольше, видеокарта свободнее", variable=mode,
                        value="gentle").pack(anchor="w", pady=(4, 0))

        memo = tk.BooleanVar(value=self.store.memo)
        ttk.Checkbutton(body, text="Сделать мемо через Claude", variable=memo, style="Switch.TCheckbutton").grid(
            row=5, column=1, columnspan=2, sticky="w", pady=(12, 0))

        is_video = video.suffix.lower() in VIDEO_EXT
        compress = tk.BooleanVar(value=self.store.compress and is_video)
        delete_original = tk.BooleanVar(value=self.store.delete_original)
        ttk.Checkbutton(body, text="Сжать видео в H.265 после транскрибации", variable=compress,
                        style="Switch.TCheckbutton", state="normal" if is_video else "disabled",
                        command=lambda: delete_box.config(state="normal" if compress.get() else "disabled")).grid(
            row=6, column=1, columnspan=2, sticky="w", pady=(10, 0))
        hint = (f"Рядом с записью появится «{compressed_path(video).name}», обычно около 10 % размера."
                if is_video else "Это аудиофайл, сжимать нечего.")
        ttk.Label(body, text=hint, foreground=self.muted).grid(row=7, column=1, columnspan=2, sticky="w",
                                                               padx=(48, 0), pady=(2, 0))
        delete_box = ttk.Checkbutton(body, text="Удалить оригинал после проверки сжатого, безвозвратно",
                                     variable=delete_original,
                                     state="normal" if compress.get() else "disabled")
        delete_box.grid(row=8, column=1, columnspan=2, sticky="w", padx=(44, 0), pady=(6, 0))

        def finish(accepted: bool) -> None:
            if accepted:
                clean = sanitize(name.get())
                if not clean:
                    messagebox.showwarning("Новая запись", "Введите название.", parent=dialog)
                    return
                self.enqueue(video, clean, folder.get(), mode.get(), memo.get(),
                             compress.get(), delete_original.get(), remember_compress=is_video)
            dialog.destroy()
            self.dialog = None
            with self.store.lock:
                self.store.known.add(str(video))
                self.store.save()
            if self.prompts:
                self.root.after(300, lambda: self.ask(self.prompts.popleft()))

        actions = ttk.Frame(body)
        actions.grid(row=9, column=0, columnspan=3, sticky="e", pady=(18, 0))
        self.button(actions, "В очередь", "play", lambda: finish(True), accent=True).pack(side="left", padx=(0, 8))
        self.button(actions, "Пропустить", "remove", lambda: finish(False)).pack(side="left")
        dialog.protocol("WM_DELETE_WINDOW", lambda: finish(False))
        dialog.bind("<Return>", lambda event: finish(True))
        dialog.bind("<Escape>", lambda event: finish(False))

        dark_title_bar(dialog, self.dark)
        x = (dialog.winfo_screenwidth() - dialog.winfo_reqwidth()) // 2
        y = (dialog.winfo_screenheight() - dialog.winfo_reqheight()) // 3
        dialog.geometry(f"+{x}+{y}")
        dialog.deiconify()
        dialog.lift()
        dialog.focus_force()
        entry.focus_set()
        entry.icursor("end")

    def enqueue(self, video: Path, name: str, out_dir: str, mode: str, memo: bool, compress: bool,
                delete_original: bool, remember_compress: bool = True) -> None:
        with self.store.lock:
            taken = {(job["out_dir"], job["name"]) for job in self.store.jobs if job["status"] != "cancelled"}
            base, number = name, 2
            while (out_dir, name) in taken or (Path(out_dir) / f"{name}.txt").exists():
                name, number = f"{base} ({number})", number + 1
            plan = "транскрибация" + (", мемо" if memo else "") + (", сжатие видео" if compress else "")
            if compress and delete_original:
                plan += " с удалением оригинала"
            self.store.jobs.append({
                "id": uuid.uuid4().hex[:8], "video": str(video), "name": name, "out_dir": out_dir,
                "mode": mode, "memo": memo, "compress": compress, "delete_original": compress and delete_original,
                "status": "waiting", "progress": 0.0, "transcript": "", "memo_file": "", "compressed": "",
                "note": "", "log": [], "added": datetime.now().isoformat(timespec="seconds"),
                "journal": [[f"{datetime.now():%H:%M:%S}", "stage",
                             f"Поставлена в очередь: {plan}, сохранить в {out_dir}"]],
            })
            self.store.last_out_dir, self.store.mode, self.store.memo = out_dir, mode, memo
            # для аудиофайла переключатель сжатия выключен, его выбор не запоминается
            if remember_compress:
                self.store.compress, self.store.delete_original = compress, delete_original
            self.store.save()
        self.sync_out_dirs()
        self.worker.wake.set()
        self.refresh()

    # --- кнопки окна ---

    def add_file(self) -> None:
        chosen = filedialog.askopenfilename(title="Запись встречи", filetypes=MEDIA_TYPES,
                                            initialdir=str(self.store.watch_dir))
        if chosen:
            self.ask(Path(chosen))

    def move_up(self) -> None:
        job = self.selected()
        if job is None:
            return
        with self.store.lock:
            jobs = self.store.jobs
            index = jobs.index(job)
            if index > 0:
                jobs[index - 1], jobs[index] = jobs[index], jobs[index - 1]
                self.store.save()
        self.refresh()

    def toggle_mode(self) -> None:
        job = self.selected()
        if job is None:
            return
        if job["status"] != "waiting":
            messagebox.showinfo(TITLE, "Режим меняется только у встреч, которые ждут в очереди.", parent=self.root)
            return
        with self.store.lock:
            job["mode"] = "gentle" if job["mode"] == "fast" else "fast"
            self.store.save()
        self.refresh()

    def retry(self) -> None:
        """Повторяет то, что не получилось. Готовые транскрипция и сжатие не повторяются.

        Если всё уже сделано, мемо делается заново, а если его не заказывали, делается впервые.
        """
        job = self.selected()
        if job is None or job["status"] in ACTIVE + ("waiting",):
            return
        has_transcript = has_file(job, "transcript")
        has_memo = has_file(job, "memo_file")
        compress_left = compression_pending(job)
        redo_memo = has_transcript and not compress_left and (has_memo or not job["memo"])
        if redo_memo and has_memo and not messagebox.askyesno(
                TITLE, "Мемо уже есть. Сделать его заново?", parent=self.root):
            return
        with self.store.lock:
            if not has_transcript:
                job["transcript"], job["memo_file"] = "", ""
            elif redo_memo:
                job["memo"], job["memo_file"] = True, ""
            job.update(status="waiting", progress=0.0, note="")
            self.store.save()
        stages = [] if has_transcript else ["транскрибация"]
        if job["memo"] and not has_file(job, "memo_file"):
            stages.append("мемо")
        if compress_left:
            stages.append("сжатие видео")
        self.worker.log(job, "Повтор: " + ", ".join(stages), "stage")
        self.worker.wake.set()
        self.refresh()

    def open_path(self, path: str) -> None:
        try:
            os.startfile(path)
        except OSError as error:
            messagebox.showerror(TITLE, f"Не удалось открыть {path}: {error}", parent=self.root)

    def selected_or_hint(self) -> dict | None:
        job = self.selected()
        if job is None:
            messagebox.showinfo(TITLE, "Выберите встречу в списке.", parent=self.root)
        return job

    def open_folder(self) -> None:
        job = self.selected_or_hint()
        if job is not None:
            self.open_path(job["out_dir"])

    def open_job_file(self, key: str) -> None:
        job = self.selected_or_hint()
        if job is None:
            return
        if job.get(key) and Path(job[key]).exists():
            self.open_path(job[key])
        else:
            what = "Мемо" if key == "memo_file" else "Транскрипции"
            messagebox.showinfo(TITLE, f"{what} у этой встречи пока нет.", parent=self.root)

    def context_menu(self, event: tk.Event) -> None:
        row = self.tree.identify_row(event.y)
        if row:
            self.tree.selection_set(row)
            self.menu.tk_popup(event.x_root, event.y_root)

    def remove(self) -> None:
        job = self.selected()
        if job is None:
            return
        if job is self.worker.current:
            if messagebox.askyesno(TITLE, "Прервать обработку этой встречи?", parent=self.root):
                self.worker.cancel()
            return
        with self.store.lock:
            self.store.jobs.remove(job)
            self.store.save()
        self.refresh()

    def clear_finished(self) -> None:
        with self.store.lock:
            self.store.jobs = [job for job in self.store.jobs if job["status"] not in FINISHED]
            self.store.save()
        self.refresh()

    def open_result(self) -> None:
        """Открывает мемо, а если его нет, транскрипцию."""
        job = self.selected_or_hint()
        if job is None:
            return
        for key in ("memo_file", "transcript"):
            if job.get(key) and Path(job[key]).exists():
                self.open_path(job[key])
                return
        messagebox.showinfo(TITLE, "Результата пока нет.", parent=self.root)

    def details(self) -> None:
        job = self.selected_or_hint()
        if job is None:
            return
        with self.store.lock:
            job = dict(job)
        window = tk.Toplevel(self.root)
        window.withdraw()
        window.title(job["name"])
        window.geometry("820x520")
        colors = {"background": "#1c1c1c", "foreground": "#e4e4e4", "insertbackground": "#e4e4e4"} \
            if self.dark else {"background": "#ffffff", "foreground": "#1a1a1a"}
        text = tk.Text(window, wrap="word", padx=14, pady=12, font=("Segoe UI Variable Text", 10),
                       borderwidth=0, highlightthickness=0, **colors)
        lines = [
            f"Встреча: {job['name']}",
            f"Видео: {job['video']}",
            f"Папка: {job['out_dir']}",
            f"Режим: {MODES[job['mode']]}",
            f"Статус: {status_text(job)}",
            f"Транскрипция: {job.get('transcript') or 'нет'}",
            f"Мемо: {job.get('memo_file') or 'нет'}",
            f"Сжатое видео: {job.get('compressed') or 'нет'}"
            + (f" ({job['compress_result']})" if job.get("compress_result") else ""),
            "",
            "Ответ Claude или сообщение об ошибке:",
            job.get("note") or "нет",
            "",
            "Ход работы:",
            *(f"{stamp}  {text}" for stamp, level, text in journal_entries(job)),
        ]
        text.insert("1.0", "\n".join(lines))
        text.configure(state="disabled")
        bar = ttk.Frame(window, padding=(14, 10))
        bar.pack(side="bottom", fill="x")
        self.button(bar, "Открыть папку", "folder", self.open_folder).pack(side="left")
        ttk.Button(bar, text="Закрыть", command=window.destroy).pack(side="right")
        text.pack(fill="both", expand=True)
        dark_title_bar(window, self.dark)
        window.deiconify()

    def on_watch_toggle(self) -> None:
        with self.store.lock:
            self.store.watch = self.watch_var.get()
            self.store.save()
        self.tray.update_menu()
        self.refresh()

    def change_watch_dir(self) -> None:
        chosen = filedialog.askdirectory(parent=self.root, initialdir=str(self.store.watch_dir))
        if not chosen:
            return
        with self.store.lock:
            self.store.watch_dir = Path(chosen)
            self.store.known |= set(list_videos(self.store.watch_dir))
            self.store.save()
        self.watch_label.config(text=str(self.store.watch_dir))
        self.refresh()

    def on_startup_toggle(self) -> None:
        try:
            set_autostart(self.startup_var.get())
        except (OSError, subprocess.CalledProcessError) as error:
            messagebox.showerror(TITLE, f"Не удалось изменить автозапуск: {error}", parent=self.root)
        self.startup_var.set(STARTUP_LINK.exists())


def main() -> int:
    if "--write-icons" in sys.argv:
        write_icons()
        return 0
    if not single_instance():
        root = tk.Tk()
        root.withdraw()
        messagebox.showinfo(TITLE, f"{TITLE} уже запущен, значок в трее.")
        return 0
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
        # свой идентификатор приложения, чтобы на панели задач была иконка Memo Maker, а не Python
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(APP_ID)
    except (AttributeError, OSError):
        pass
    if not (ICON.exists() and ICON_BUSY.exists()):
        write_icons()
    App(hidden="--hidden" in sys.argv).root.mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
