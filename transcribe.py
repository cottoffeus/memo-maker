"""Транскрибация записей встреч и других видео на своей машине через faster-whisper.

Звук распознаётся на видеокарте моделью Whisper large-v3, результат пишется
текстом с метками времени, по фразе на строку, с пунктуацией и заглавными
буквами. Запись никуда не отправляется: модель лежит в локальном кэше
Hugging Face, сеть нужна только для первой загрузки модели.

Скрипт запускается интерпретатором Python 3.12, в котором установлены пакеты
из requirements.txt: faster-whisper и библиотеки CUDA (nvidia-cublas-cu12,
nvidia-cudnn-cu12).

Примеры:
    py -3.12 transcribe.py "%USERPROFILE%/Videos/2026-10-01 11-19-11.mp4"
    py -3.12 transcribe.py "<видео>" --title "Синк по сервису меню" --out "<папка>"
    py -3.12 transcribe.py "<видео>" --name "2026 10 01 Синк по меню" --mode gentle
    py -3.12 transcribe.py "<видео>" --format srt

По умолчанию файл кладётся в текущую папку под именем видео. С флагом
--title имя собирается как "2026 10 01 <тема>.txt":
дата берётся из имени файла OBS, а если её там нет, из даты изменения файла.
Флаг --name задаёт имя целиком.

Оба режима считают в int8: на GTX 1660 Ti это вдвое быстрее float16
и требует около 2,3 ГБ видеопамяти вместо 4,2 ГБ при том же качестве текста.
Замер на 10 минутах записи: fast за 1,1 минуты при средней загрузке
видеокарты 56%, gentle за 3,1 минуты при загрузке 30%. Режим gentle после
каждой фразы делает паузу вдвое длиннее времени счёта и понижает приоритет
процесса. Нарезать запись на куски не нужно: модель и так обрабатывает звук
окнами по 30 секунд, и расход видеопамяти от длины записи не зависит.

Модель сначала ищется в общей папке C:/ProgramData/MemoMaker/models, которую
читают все пользователи компьютера. Если она там есть, загрузка идёт без сети
и без записи в папку. Если нет, модель скачивается в кэш Hugging Face
текущего пользователя.

Пока идёт работа, результат пишется во временный файл с расширением .part,
готовый файл появляется только после завершения.
"""

from __future__ import annotations

import argparse
import ctypes
import glob
import os
import re
import site
import sys
import time
from datetime import datetime
from pathlib import Path

OBS_DATE = re.compile(r"(\d{4})-(\d{2})-(\d{2})")
BELOW_NORMAL_PRIORITY_CLASS = 0x4000
SHARED_MODELS = Path(os.environ.get("PROGRAMDATA", "C:/ProgramData")) / "MemoMaker" / "models"

# тип вычислений на видеокарте и пауза после каждой фразы в долях от времени счёта
MODES = {
    "fast": ("int8_float16", 0.0),
    "gentle": ("int8_float16", 2.0),
}

# Подсказка подаётся модели в каждом окне распознавания. Без неё Whisper
# иногда пишет целые куски строчными буквами и без знаков препинания.
STYLE_HINT = "Рабочая встреча, обсуждаем задачи, сроки и решения."

# фразы склеиваются в абзац, пока между ними нет паузы и абзац не слишком длинный
PARAGRAPH_GAP = 2.0
PARAGRAPH_CHARS = 400


def enable_cuda_dlls() -> None:
    """Делает DLL из pip-пакетов nvidia-* видимыми для ctranslate2 на Windows."""
    for base in site.getsitepackages():
        for path in glob.glob(os.path.join(base, "nvidia", "*", "bin")):
            os.add_dll_directory(path)
            os.environ["PATH"] = path + os.pathsep + os.environ["PATH"]


def lower_priority() -> None:
    if os.name == "nt":
        kernel32 = ctypes.windll.kernel32
        kernel32.SetPriorityClass(kernel32.GetCurrentProcess(), BELOW_NORMAL_PRIORITY_CLASS)


def shared_model_root(name: str) -> str | None:
    """Общая папка моделей, если в ней уже лежит нужная модель, иначе None."""
    try:
        from faster_whisper.utils import _MODELS
        repo = _MODELS.get(name, name)
    except ImportError:
        repo = f"Systran/faster-whisper-{name}"
    folder = SHARED_MODELS / ("models--" + repo.replace("/", "--"))
    return str(SHARED_MODELS) if any(folder.glob("snapshots/*/model.bin")) else None


def recording_date(video: Path) -> str:
    match = OBS_DATE.search(video.stem)
    if match:
        return " ".join(match.groups())
    return datetime.fromtimestamp(video.stat().st_mtime).strftime("%Y %m %d")


def hms(seconds: float) -> str:
    total = int(seconds)
    return f"{total // 3600:02}:{total % 3600 // 60:02}:{total % 60:02}"


def srt_time(seconds: float) -> str:
    ms = int(round(seconds * 1000))
    hours, ms = divmod(ms, 3_600_000)
    minutes, ms = divmod(ms, 60_000)
    secs, ms = divmod(ms, 1000)
    return f"{hours:02}:{minutes:02}:{secs:02},{ms:03}"


def main() -> int:
    parser = argparse.ArgumentParser(description="Распознаёт речь в видео или аудио и пишет текст с метками времени.")
    parser.add_argument("video", type=Path, help="видео или аудиофайл")
    naming = parser.add_mutually_exclusive_group()
    naming.add_argument("--title", help='тема встречи, имя файла будет "ГГГГ ММ ДД <тема>"')
    naming.add_argument("--name", help="имя файла целиком, без расширения")
    parser.add_argument("--out", type=Path, default=Path.cwd(), help="папка для результата, по умолчанию текущая")
    parser.add_argument("--format", choices=["txt", "srt"], default="txt",
                        help="txt: фраза на строку с меткой времени; srt: субтитры")
    parser.add_argument("--mode", choices=sorted(MODES), default="fast",
                        help="fast: вся мощность видеокарты; gentle: вдвое дольше, видеокарта свободнее")
    parser.add_argument("--compute-type", help="тип вычислений вместо заданного режимом, например float16")
    parser.add_argument("--model", default="large-v3", help="модель Whisper, по умолчанию large-v3")
    parser.add_argument("--language", default="ru", help="язык речи, по умолчанию ru")
    parser.add_argument("--prompt", help="подсказка модели: термины и названия, которые звучат на встрече")
    parser.add_argument("--device", choices=["cuda", "cpu"], default="cuda", help="на чём считать")
    parser.add_argument("--force", action="store_true", help="перезаписать существующий файл")
    args = parser.parse_args()

    video = args.video.resolve()
    if not video.exists():
        print(f"нет файла: {video}")
        return 1
    if args.name:
        name = args.name
    elif args.title:
        name = f"{recording_date(video)} {args.title}"
    else:
        name = video.stem
    target = args.out / f"{name}.{args.format}"
    if target.exists() and not args.force:
        print(f"файл уже есть, перезапись флагом --force: {target}")
        return 1
    args.out.mkdir(parents=True, exist_ok=True)

    compute_type, pause = MODES[args.mode]
    if args.mode == "gentle":
        lower_priority()
    if args.device == "cuda":
        enable_cuda_dlls()
    else:
        compute_type = "int8"
    compute_type = args.compute_type or compute_type
    from faster_whisper import WhisperModel

    started = time.time()
    print(f"Загрузка модели {args.model}, вычисления {compute_type}", flush=True)
    shared = shared_model_root(args.model)
    model = WhisperModel(args.model, device=args.device, compute_type=compute_type,
                         download_root=shared, local_files_only=shared is not None)
    print("Разбор звука и поиск фрагментов с речью", flush=True)
    segments, info = model.transcribe(
        str(video),
        language=args.language,
        hotwords=f"{STYLE_HINT} {args.prompt}" if args.prompt else STYLE_HINT,
        beam_size=5,
        vad_filter=True,
        condition_on_previous_text=False,
    )

    print(f"Длительность записи {hms(info.duration)}, распознавание началось", flush=True)
    interactive = sys.stdout.isatty()
    partial = target.with_name(target.name + ".part")
    count = 0
    paragraph: list[str] = []
    paragraph_start = paragraph_end = 0.0
    with partial.open("w", encoding="utf-8") as out:

        def flush() -> None:
            if paragraph:
                out.write(f"[{hms(paragraph_start)}] {' '.join(paragraph)}\n")
                out.flush()
                paragraph.clear()

        mark = time.time()
        for segment in segments:
            text = segment.text.strip()
            if text:
                count += 1
                if args.format == "srt":
                    out.write(f"{count}\n{srt_time(segment.start)} --> {srt_time(segment.end)}\n{text}\n\n")
                    out.flush()
                else:
                    if paragraph and (segment.start - paragraph_end > PARAGRAPH_GAP
                                      or sum(map(len, paragraph)) > PARAGRAPH_CHARS):
                        flush()
                    if not paragraph:
                        paragraph_start = segment.start
                    paragraph.append(text)
                    paragraph_end = segment.end
            done = min(segment.end / info.duration, 1.0) if info.duration else 0.0
            line = f"{done:6.1%}  {hms(segment.end)} из {hms(info.duration)}"
            print("\r" + line if interactive else line, end="" if interactive else "\n", flush=True)
            if pause:
                time.sleep((time.time() - mark) * pause)
            mark = time.time()
        flush()
    os.replace(partial, target)

    elapsed = time.time() - started
    print(f"\nГотово: {count} фраз, {info.duration / 60:.0f} мин записи за {elapsed / 60:.1f} мин")
    print(target)
    return 0


if __name__ == "__main__":
    sys.exit(main())
