from __future__ import annotations

import queue
import re
import ssl
import threading
import time
import gzip
import io
import tkinter as tk
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from dataclasses import dataclass, field
from datetime import date, datetime
from html.parser import HTMLParser
from http.client import HTTPSConnection
from tkinter import ttk
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, urljoin, urlsplit
from urllib.request import HTTPSHandler, Request, build_opener


SITE = "https://natk.ru"
INDEX_URL = SITE + "/stud-grad/schedule"
ADDRESS = "Красный проспект, 72"
CACHE_SECONDS = 180
SEARCH_SECONDS = 90
MAX_PAGE_BYTES = 4_000_000
MONTHS = (
    "января", "февраля", "марта", "апреля", "мая", "июня",
    "июля", "августа", "сентября", "октября", "ноября", "декабря",
)
DATE_RE = re.compile(r"(\d{1,2})\s+(" + "|".join(MONTHS) + r")\s+(\d{4})", re.I)
TIME_RE = re.compile(r"(\d{1,2}:\d{2})\s*[-–—]\s*(\d{1,2}:\d{2})")
ADDRESS_RE = re.compile(r"Красный\s+проспект\s*,?\s*(?:д\.?\s*)?72(?![\w/\-])", re.I)
ROOM_RE = re.compile(r"(?:кабинет|аудитория|мастерская|лаборатория)\s*№?\s*(\d+[а-яёa-z]*)\b", re.I)


def compact(text: str) -> str:
    return " ".join(text.split())


def parse_date(text: str) -> date:
    text = text.strip()
    if re.fullmatch(r"\d{1,2}\.\d{1,2}", text):
        text += f".{date.today().year}"
    if not re.fullmatch(r"\d{1,2}\.\d{1,2}\.\d{4}", text):
        raise ValueError("Введите дату в формате ДД.ММ.ГГГГ, например 12.10.2026.")
    try:
        return datetime.strptime(text, "%d.%m.%Y").date()
    except ValueError:
        raise ValueError("Такой даты не существует. Проверьте день, месяц и год.") from None


def parse_room(text: str) -> str:
    text = text.strip().removeprefix("№").strip()
    if not re.fullmatch(r"\d{1,4}[а-яёa-z]{0,3}", text, re.I):
        raise ValueError("Введите номер аудитории, например 103, 368 или 485А.")
    return text.upper()


@dataclass
class Cell:
    parts: list[str] = field(default_factory=list)
    spans: list[str] = field(default_factory=list)
    links: list[tuple[str, str]] = field(default_factory=list)

    @property
    def text(self) -> str:
        return compact(" ".join(self.parts))


class ScheduleHTML(HTMLParser):
    """Читает ссылки и таблицы, включая HTML с незакрытыми тегами tr."""

    def __init__(self, all_tables: bool = False) -> None:
        super().__init__(convert_charrefs=True)
        self.all_tables = all_tables
        self.groups: dict[str, str] = {}
        self.rows: list[list[Cell]] = []
        self.tables_found = 0
        self.depth = 0
        self.row: list[Cell] = []
        self.cell: Cell | None = None
        self.span_depth = 0
        self.span_parts: list[str] = []
        self.anchor_href = ""
        self.anchor_parts: list[str] = []

    def finish_cell(self) -> None:
        if self.cell is not None:
            if self.anchor_href:
                self.cell.links.append((self.anchor_href, compact(" ".join(self.anchor_parts))))
            if self.span_depth:
                self.cell.spans.append(compact(" ".join(self.span_parts)))
            self.row.append(self.cell)
        self.cell = None
        self.span_depth = 0
        self.span_parts = []
        self.anchor_href = ""
        self.anchor_parts = []

    def finish_row(self) -> None:
        self.finish_cell()
        if self.row:
            self.rows.append(self.row)
        self.row = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attributes = dict(attrs)
        if tag == "a":
            href = attributes.get("href") or ""
            url = urljoin(INDEX_URL, href)
            parsed = urlsplit(url)
            gid = parse_qs(parsed.query).get("gid", [""])[0]
            if parsed.hostname == "natk.ru" and "/schedule/187" in parsed.path and gid.isdigit():
                self.groups[gid] = SITE + "/stud-grad/schedule/187?gid=" + gid
            if self.cell is not None:
                self.anchor_href = url
                self.anchor_parts = []
        if tag == "table":
            if self.depth:
                self.depth += 1
            elif self.all_tables or "sura_shedule" in (attributes.get("class") or "").split():
                self.depth = 1
                self.tables_found += 1
            return
        if not self.depth:
            return
        if tag == "tr":
            self.finish_row()
        elif tag in ("td", "th"):
            self.finish_cell()
            self.cell = Cell()
        elif tag == "span" and self.cell is not None:
            if not self.span_depth:
                self.span_parts = []
            self.span_depth += 1

    def handle_data(self, data: str) -> None:
        if self.cell is not None:
            self.cell.parts.append(data)
            if self.anchor_href:
                self.anchor_parts.append(data)
            if self.span_depth:
                self.span_parts.append(data)

    def handle_endtag(self, tag: str) -> None:
        if not self.depth:
            return
        if tag == "a" and self.anchor_href and self.cell is not None:
            self.cell.links.append((self.anchor_href, compact(" ".join(self.anchor_parts))))
            self.anchor_href = ""
            self.anchor_parts = []
        elif tag == "span" and self.span_depth:
            self.span_depth -= 1
            if not self.span_depth and self.cell is not None:
                self.cell.spans.append(compact(" ".join(self.span_parts)))
                self.span_parts = []
        elif tag in ("td", "th"):
            self.finish_cell()
        elif tag == "tr":
            self.finish_row()
        elif tag == "table":
            self.depth -= 1
            if not self.depth:
                self.finish_row()

    def close(self) -> None:
        super().close()
        self.finish_row()


@dataclass(frozen=True, order=True)
class Lesson:
    start: str
    end: str
    room: str
    teacher: str

    def line(self) -> str:
        return f"{self.start} {self.room} {self.teacher} до {self.end}"


@dataclass
class DayResult:
    lessons: list[Lesson] = field(default_factory=list)
    has_date: bool = False
    missing_info: bool = False
    warnings: list[str] = field(default_factory=list)
    teachers: dict[str, str] = field(default_factory=dict)


def extract_lessons(source: str, wanted_date: date, room: str, teacher_override: str | None = None) -> DayResult:
    parser = ScheduleHTML(all_tables=bool(teacher_override))
    parser.feed(source)
    parser.close()
    if not parser.tables_found:
        raise ValueError("На странице не найдена таблица расписания; возможно, формат сайта изменился.")
    result = DayResult()
    active = False
    current_time: tuple[str, str] | None = None
    for row in parser.rows:
        row_text = " ".join(cell.text for cell in row)
        day_match = DATE_RE.search(row_text) if len(row) == 1 else None
        if day_match:
            day, month, year = day_match.groups()
            parsed_day = date(int(year), MONTHS.index(month.lower()) + 1, int(day))
            active = parsed_day == wanted_date
            result.has_date |= active
            current_time = None
            continue
        if not active:
            continue
        if "информация отсутствует" in row_text.lower():
            result.missing_info = True
        time_match = TIME_RE.search(row_text)
        if time_match:
            current_time = tuple(value.zfill(5) for value in time_match.groups())
        elif row and (row[0].text.isdigit() or re.search(r"\b\d{1,2}:\d{2}\b", row[0].text)):
            # Экзамен может иметь только начало: не заимствуем время предыдущей пары.
            current_time = None
        for cell in row:
            # В одной ячейке могут находиться несколько занятий/подгрупп.
            locations = [(i, span) for i, span in enumerate(cell.spans) if ADDRESS_RE.search(span)]
            if not locations and ADDRESS_RE.search(cell.text):
                locations = [(-1, cell.text)]
            for position, location in locations:
                if not any(m.group(1).casefold() == room.casefold() for m in ROOM_RE.finditer(location)):
                    continue
                teacher = teacher_override or (cell.spans[position - 1] if position >= 2 else "")
                teacher_links = [(url, name) for url, name in cell.links if "/sveden/teachers/" in url or "/sveden/chief/" in url]
                if not teacher and teacher_links:
                    teacher = teacher_links[-1][1]
                teacher = teacher or "Преподаватель не указан"
                for url, name in teacher_links:
                    if name == teacher and urlsplit(url).hostname in {"natk.ru", "www.natk.ru"}:
                        result.teachers[url] = name
                if current_time is None:
                    start_match = re.search(r"\b\d{1,2}:\d{2}\b", row_text)
                    start = start_match.group().zfill(5) if start_match else "??:??"
                    start_end = (start, "??:??")
                    result.warnings.append("Для одного из занятий сайт не указал полный интервал времени.")
                else:
                    start_end = current_time
                if teacher == "Преподаватель не указан":
                    result.warnings.append("Для одного из занятий не удалось прочитать преподавателя.")
                result.lessons.append(Lesson(*start_end, room, teacher))
    return result


class Cancelled(Exception):
    pass


class NatkHTTPSHandler(HTTPSHandler):
    """Обход сертификата только у НАТК, без лишнего неудачного TLS-запроса."""

    def __init__(self):
        super().__init__(context=VERIFIED_CONTEXT)

    def https_open(self, request):
        if urlsplit(request.full_url).hostname in {"natk.ru", "www.natk.ru"}:
            return self.do_open(HTTPSConnection, request, context=NATK_CONTEXT)
        return super().https_open(request)


# Контексты создаются один раз, а не при загрузке каждой группы.
VERIFIED_CONTEXT = ssl.create_default_context()
NATK_CONTEXT = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
NATK_CONTEXT.check_hostname = False
NATK_CONTEXT.verify_mode = ssl.CERT_NONE
NETWORK_LOCAL = threading.local()


def fetch(url: str, stop: threading.Event, timeout: float = 8) -> str:
    if stop.is_set():
        raise Cancelled()
    opener = getattr(NETWORK_LOCAL, "opener", None)
    if opener is None:
        opener = NETWORK_LOCAL.opener = build_opener(NatkHTTPSHandler())
    request = Request(url, headers={
        "User-Agent": "Mozilla/5.0 NATK-Room-Schedule/2.0",
        "Accept": "text/html", "Accept-Encoding": "gzip",
        "Cache-Control": "no-cache",
    })
    with opener.open(request, timeout=max(0.1, timeout)) as response:
        raw = response.read(MAX_PAGE_BYTES + 1)
        if len(raw) > MAX_PAGE_BYTES:
            raise ValueError("Слишком большая страница расписания.")
        if response.headers.get("Content-Encoding", "").lower() == "gzip":
            with gzip.GzipFile(fileobj=io.BytesIO(raw)) as compressed:
                raw = compressed.read(MAX_PAGE_BYTES + 1)
            if len(raw) > MAX_PAGE_BYTES:
                raise ValueError("Слишком большая страница расписания.")
        if stop.is_set():
            raise Cancelled()
        return raw.decode(response.headers.get_content_charset() or "utf-8")


def error_message(error: Exception) -> str:
    if isinstance(error, HTTPError):
        return f"HTTP {error.code}: {error.reason}"
    reason = error.reason if isinstance(error, URLError) else error
    if isinstance(reason, TimeoutError):
        return "тайм-аут: сайт не ответил вовремя"
    if isinstance(reason, ssl.SSLError):
        return f"ошибка TLS: {reason}"
    return f"{type(reason).__name__}: {reason}"


class PageCache:
    """Только оперативная память. Никаких файлов и сохранений на диск."""

    def __init__(self):
        self.pages: dict[str, tuple[float, str]] = {}

    def get(self, url: str) -> str | None:
        entry = self.pages.get(url)
        if entry and time.monotonic() - entry[0] < CACHE_SECONDS:
            return entry[1]
        self.pages.pop(url, None)
        return None

    def put(self, url: str, source: str) -> None:
        self.pages[url] = (time.monotonic(), source)
        # Ограничение памяти при длительной работе с разными аудиториями.
        while len(self.pages) > 180:
            self.pages.pop(next(iter(self.pages)))

    def purge(self) -> None:
        now = time.monotonic()
        for url in list(self.pages):
            if now - self.pages[url][0] >= CACHE_SECONDS:
                self.pages.pop(url, None)

    def clear(self) -> None:
        self.pages.clear()


def download_batch(urls, stop, deadline, workers, timeout, consume):
    """Ограниченное число запросов; результат отдаётся по мере готовности."""
    pending_urls = iter(urls)
    pool = ThreadPoolExecutor(max_workers=workers)
    futures = {}
    received = failures = 0

    def fill():
        while len(futures) < workers and not stop.is_set() and time.monotonic() < deadline:
            url = next(pending_urls, None)
            if url is None:
                break
            remaining = deadline - time.monotonic()
            futures[pool.submit(fetch, url, stop, min(timeout, remaining))] = url

    try:
        fill()
        while futures and not stop.is_set() and time.monotonic() < deadline:
            ready, _ = wait(futures, timeout=0.1, return_when=FIRST_COMPLETED)
            for future in ready:
                url = futures.pop(future)
                try:
                    source = future.result()
                    consume(url, source, None)
                    received += 1
                except Exception as error:
                    consume(url, None, error)
                    failures += 1
            # При полном обрыве связи не ждём тайм-аут для каждой из сотни групп.
            if received == 0 and failures >= workers:
                break
            fill()
    finally:
        for future in futures:
            future.cancel()
        pool.shutdown(wait=False, cancel_futures=True)


def search(wanted_date: date, room: str, stop: threading.Event, events: queue.Queue,
           cache: PageCache | None = None, force: bool = False) -> None:
    cache = cache if cache is not None else PageCache()
    cache.purge()
    if force:
        cache.clear()
    started = time.monotonic()
    deadline = started + SEARCH_SECONDS
    days: dict[str, DayResult] = {}
    errors: dict[str, str] = {}
    attempts: dict[str, int] = {}
    teacher_days: dict[str, DayResult] = {}
    teacher_checked: set[str] = set()
    notes: list[str] = []
    urls: list[str] = []
    reused = 0
    phase = "Проверяю группы"
    last_lines = None

    def all_lessons():
        return {lesson for day in [*days.values(), *teacher_days.values()] for lesson in day.lessons}

    def publish():
        nonlocal last_lines
        lines = "\n".join(lesson.line() for lesson in sorted(all_lessons()))
        if lines != last_lines:
            events.put(("partial", lines))
            last_lines = lines
        events.put(("progress", len(days), len(urls), phase))

    def consume(url, source, error):
        attempts[url] = attempts.get(url, 0) + 1
        if error is None:
            try:
                day = extract_lessons(source, wanted_date, room)
                days[url] = day
                cache.put(url, source)
                errors.pop(url, None)
            except Exception as parse_error:
                errors[url] = error_message(parse_error)
        else:
            errors[url] = error_message(error)
        publish()

    def check_teachers():
        nonlocal phase
        teachers = {url: name for day in days.values() for url, name in day.teachers.items()}
        teacher_urls = [url for url in teachers if url not in teacher_checked]
        if not teacher_urls or stop.is_set() or time.monotonic() >= deadline:
            return
        phase = "Сверяю расписания преподавателей"
        publish()
        needed = []

        def accept_teacher(url, source, error):
            teacher_checked.add(url)
            if error is not None:
                notes.append(f"Не удалось сверить преподавателя: {error_message(error)} — {url}")
                return
            try:
                day = extract_lessons(source, wanted_date, room, teacher_override=teachers[url])
                cache.put(url, source)
                if day.has_date:
                    teacher_days[url] = day
                    notes.append(f"Сверено расписание: {teachers[url]} — {url}")
                else:
                    notes.append(f"У преподавателя нет выбранной даты: {url}")
            except Exception as error:
                notes.append(f"Не удалось разобрать расписание преподавателя: {error_message(error)} — {url}")
            publish()

        for url in teacher_urls:
            saved = cache.get(url)
            if saved is None:
                needed.append(url)
            else:
                accept_teacher(url, saved, None)
        download_batch(needed, stop, min(deadline, time.monotonic() + 12), 3, 6, accept_teacher)

    try:
        source = cache.get(INDEX_URL)
        index_downloaded = source is None
        if source is None:
            # Индекс небольшой: один быстрый повтор при кратком разрыве связи.
            for attempt in range(2):
                try:
                    source = fetch(INDEX_URL, stop, timeout=7)
                    break
                except Cancelled:
                    raise
                except Exception:
                    if attempt == 1:
                        raise
                    if stop.wait(0.3):
                        raise Cancelled()
        index = ScheduleHTML()
        index.feed(source)
        index.close()
        urls = list(index.groups.values())
        if not urls:
            raise ValueError("Не найдены ссылки на группы. Возможно, сайт изменил формат расписания.")
        if index_downloaded:
            cache.put(INDEX_URL, source)
        for url in urls:
            saved = cache.get(url)
            if saved is not None:
                try:
                    day = extract_lessons(saved, wanted_date, room)
                    if day.has_date:
                        days[url] = day
                        reused += 1
                except ValueError:
                    pass
        publish()
        # Сначала быстрый проход. Затем — только пропуски, с меньшей нагрузкой на сайт.
        for round_number, (workers, timeout) in enumerate(((6, 8), (3, 12), (2, 15))):
            pending = [url for url in urls if url not in days]
            if not pending or stop.is_set() or time.monotonic() >= deadline:
                break
            phase = "Загружаю группы" if round_number == 0 else f"Догружаю пропуски · попытка {round_number + 1}"
            publish()
            # Оставляем время на независимую сверку преподавателей.
            group_deadline = deadline - (12 if round_number == 0 else 0)
            download_batch(pending, stop, group_deadline, workers, timeout, consume)
            if round_number == 0:
                check_teachers()
            if round_number < 2 and any(url not in days for url in urls) and stop.wait(0.4):
                break
        # Если данные уже были в памяти, всё равно проверяем найденных преподавателей.
        if not stop.is_set():
            check_teachers()
    except Cancelled:
        pass
    except Exception as error:
        events.put(("error", f"Не удалось загрузить список групп: {error_message(error)}.\nПроверьте соединение и попробуйте без VPN."))
        return

    lessons = all_lessons()
    lines = "\n".join(lesson.line() for lesson in sorted(lessons))
    failed = len(urls) - len(days)
    no_date = sum(not day.has_date for day in days.values())
    empty = sum(day.missing_info for day in days.values())
    warnings = [f"{warning} — {url}" for url, day in {**days, **teacher_days}.items() for warning in day.warnings]
    elapsed = time.monotonic() - started
    status = f"Найдено занятий: {len(lessons)}. Загружено групп: {len(days)}/{len(urls)}. {elapsed:.1f} с."
    if reused:
        status += f" Из памяти: {reused} (не старше 3 минут)."
    if stop.is_set():
        status += " Поиск остановлен; результат неполный."
    elif failed:
        status += f" Результат может быть неполным. Не загружено: {failed}. Нажмите «Найти» для догрузки пропусков."
    elif no_date or empty:
        status += f" На сайте нет даты у {no_date} групп, нет данных у {empty}."
    elif not lessons and urls:
        status += " По опубликованному расписанию занятия не найдены."
    if warnings:
        status += " Есть замечания — см. подробности."
    details = [f"Дата: {wanted_date:%d.%m.%Y}. Аудитория: {room}. Адрес: {ADDRESS}.", status, ""]
    for url in urls:
        if url not in days:
            problem = errors.get(url, "не проверено: остановка, общий лимит времени или обрыв связи")
            details.append(f"{problem}; попыток: {attempts.get(url, 0)} — {url}")
        elif not days[url].has_date:
            details.append(f"Дата не опубликована — {url}")
        elif days[url].missing_info:
            details.append(f"На сайте указано «информация отсутствует» — {url}")
    details.extend(warnings)
    details.extend(notes)
    details.extend(["", "Источники найденных занятий:"])
    for url, day in {**days, **teacher_days}.items():
        details.extend(f"{lesson.line()} — {url}" for lesson in day.lessons)
    events.put(("done", lines, status, "\n".join(details)))


class App(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("НАТК · Расписание аудитории · 2.0")
        self.geometry("760x520")
        self.minsize(600, 430)
        self.configure(bg="#f5f6f8")
        self.events: queue.Queue = queue.Queue()
        self.cache = PageCache()
        self.stop = threading.Event()
        self.busy = False
        self.details = ""
        self.style = ttk.Style(self)
        self.style.theme_use("clam")
        self.style.configure("TFrame", background="#f5f6f8")
        self.style.configure("TLabel", background="#f5f6f8", font=("Segoe UI", 10))
        self.style.configure("TButton", font=("Segoe UI", 10), padding=(12, 7))
        self.style.configure("TEntry", padding=7)
        self.style.configure("Title.TLabel", font=("Segoe UI", 19, "bold"))
        self.style.configure("Muted.TLabel", foreground="#586174")
        body = ttk.Frame(self, padding=24)
        body.pack(fill="both", expand=True)
        ttk.Label(body, text="Расписание аудитории", style="Title.TLabel").pack(anchor="w")
        ttk.Label(body, text=f"НАТК · {ADDRESS}", style="Muted.TLabel").pack(anchor="w", pady=(3, 20))
        controls = ttk.Frame(body)
        controls.pack(fill="x")
        ttk.Label(controls, text="Дата").grid(row=0, column=0, sticky="w")
        ttk.Label(controls, text="Аудитория").grid(row=0, column=1, sticky="w", padx=(12, 0))
        self.day_var = tk.StringVar(value=date.today().strftime("%d.%m.%Y"))
        self.room_var = tk.StringVar(value="103")
        self.day_entry = ttk.Entry(controls, textvariable=self.day_var, width=18, font=("Segoe UI", 11))
        self.day_entry.grid(row=1, column=0, sticky="ew", pady=(5, 0))
        self.room_entry = ttk.Entry(controls, textvariable=self.room_var, width=12, font=("Segoe UI", 11))
        self.room_entry.grid(row=1, column=1, sticky="ew", padx=12, pady=(5, 0))
        self.search_button = ttk.Button(controls, text="Найти", command=self.start_search)
        self.search_button.grid(row=1, column=2, sticky="ew", pady=(5, 0))
        controls.columnconfigure(0, weight=1)
        controls.columnconfigure(1, weight=1)
        self.progress = ttk.Progressbar(body, mode="determinate", maximum=100)
        self.progress.pack(fill="x", pady=(18, 8))
        self.status = ttk.Label(body, text="Введите дату и номер аудитории.", style="Muted.TLabel", wraplength=690)
        self.status.pack(fill="x", pady=(0, 12))
        result_frame = ttk.Frame(body)
        result_frame.pack(fill="both", expand=True)
        self.output = tk.Text(result_frame, wrap="none", font=("Consolas", 11), bg="white", fg="#182234", relief="flat", padx=12, pady=12, state="disabled")
        self.output.grid(row=0, column=0, sticky="nsew")
        vertical = ttk.Scrollbar(result_frame, orient="vertical", command=self.output.yview)
        vertical.grid(row=0, column=1, sticky="ns")
        horizontal = ttk.Scrollbar(result_frame, orient="horizontal", command=self.output.xview)
        horizontal.grid(row=1, column=0, sticky="ew")
        self.output.configure(yscrollcommand=vertical.set, xscrollcommand=horizontal.set)
        result_frame.rowconfigure(0, weight=1)
        result_frame.columnconfigure(0, weight=1)
        footer = ttk.Frame(body)
        footer.pack(fill="x", pady=(12, 0))
        self.copy_button = ttk.Button(footer, text="Скопировать", command=self.copy_result, state="disabled")
        self.copy_button.pack(side="left")
        self.refresh_button = ttk.Button(footer, text="Обновить", command=lambda: self.start_search(force=True))
        self.refresh_button.pack(side="left", padx=(8, 0))
        self.details_button = ttk.Button(footer, text="Подробности", command=self.show_details, state="disabled")
        self.details_button.pack(side="right")
        self.bind("<Return>", lambda _event: self.start_search() if not self.busy else None)
        self.bind("<Configure>", self.resize_status)
        self.protocol("WM_DELETE_WINDOW", self.close_app)
        self.after(100, self.poll)
        self.after(30000, self.purge_cache)
        self.room_entry.focus_set()
        self.room_entry.selection_range(0, "end")

    def resize_status(self, event: tk.Event) -> None:
        if event.widget is self:
            self.status.configure(wraplength=max(300, event.width - 55))

    def set_output(self, text: str) -> None:
        self.output.configure(state="normal")
        self.output.delete("1.0", "end")
        self.output.insert("1.0", text)
        self.output.configure(state="disabled")
        self.copy_button.configure(state="normal" if text else "disabled")

    def purge_cache(self) -> None:
        if not self.busy:
            self.cache.purge()
        self.after(30000, self.purge_cache)

    def start_search(self, force: bool = False) -> None:
        if self.busy:
            self.stop.set()
            self.search_button.configure(state="disabled")
            self.status.configure(text="Останавливаю поиск…")
            return
        try:
            wanted_date = parse_date(self.day_var.get())
            room = parse_room(self.room_var.get())
        except ValueError as error:
            self.status.configure(text=str(error))
            return
        self.day_var.set(wanted_date.strftime("%d.%m.%Y"))
        self.room_var.set(room)
        self.set_output("")
        self.details = ""
        self.details_button.configure(state="disabled")
        self.busy = True
        self.stop = threading.Event()
        self.day_entry.configure(state="disabled")
        self.room_entry.configure(state="disabled")
        self.search_button.configure(text="Остановить")
        self.refresh_button.configure(state="disabled")
        self.progress.configure(value=0)
        self.status.configure(text="Получаю список групп с сайта НАТК…")
        threading.Thread(target=search, args=(wanted_date, room, self.stop, self.events, self.cache, force), daemon=True).start()

    def finish(self) -> None:
        self.busy = False
        self.search_button.configure(text="Найти", state="normal")
        self.refresh_button.configure(state="normal")
        self.day_entry.configure(state="normal")
        self.room_entry.configure(state="normal")

    def poll(self) -> None:
        try:
            while True:
                event = self.events.get_nowait()
                if event[0] == "progress":
                    _, current, total, phase = event
                    self.progress.configure(maximum=total, value=current)
                    if not self.stop.is_set():
                        self.status.configure(text=f"{phase}: {current} из {total}…")
                elif event[0] == "partial":
                    self.set_output(event[1])
                elif event[0] == "done":
                    _, lines, status, self.details = event
                    self.set_output(lines)
                    self.status.configure(text=status)
                    self.details_button.configure(state="normal")
                    self.finish()
                elif event[0] == "error":
                    self.status.configure(text=event[1])
                    self.finish()
        except queue.Empty:
            pass
        self.after(100, self.poll)

    def copy_result(self) -> None:
        self.clipboard_clear()
        self.clipboard_append(self.output.get("1.0", "end-1c"))

    def show_details(self) -> None:
        window = tk.Toplevel(self)
        window.title("Проверка расписания")
        window.geometry("720x380")
        text = tk.Text(window, wrap="word", font=("Segoe UI", 10), padx=12, pady=12)
        scrollbar = ttk.Scrollbar(window, command=text.yview)
        scrollbar.pack(side="right", fill="y")
        text.configure(yscrollcommand=scrollbar.set)
        text.pack(fill="both", expand=True)
        text.insert("1.0", self.details)
        text.configure(state="disabled")

    def close_app(self) -> None:
        self.stop.set()
        self.cache.clear()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()
