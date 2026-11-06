"""acczHELP — панель Telegram для рассылок в выбранные группы.

Render Web Service из репозитория GitHub (Python 3.10+):
    Build Command: python -m pip install aiogram==3.25.0 Telethon==1.45.0
    Start Command: python bot.py
    Health Check Path: /healthz
    Environment: API_ID, API_HASH, BOT_TOKEN, OWNER_ID.
    В меню «Вход в аккаунт» введи телефон, код Telegram и пароль 2FA, если он включён.
    Для постоянной SQLite: подключить диск в /var/data и задать DATA_DIR=/var/data.
    В UptimeRobot добавить HTTP(s)-монитор https://<имя>.onrender.com/readyz.

В GitHub помещают bot.py. Ключи и файл сессии хранятся в Render.
Один токен и одна пользовательская сессия на один процесс.
"""

# 1. Импорты
from __future__ import annotations

import argparse
import asyncio
import base64
import getpass
import html
import hmac
import io
import json
import logging
import os
import re
import secrets
import sqlite3
import struct
import sys
import tempfile
import time
from collections.abc import Awaitable, Callable, Sequence
from contextlib import contextmanager, suppress
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import TypeVar
from urllib.parse import urlsplit

from aiogram import Bot, Dispatcher, F
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ChatType, MessageEntityType, ParseMode
from aiogram.exceptions import TelegramAPIError, TelegramBadRequest, TelegramRetryAfter
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage, SimpleEventIsolation
from aiogram.types import (
    BufferedInputFile, CallbackQuery, ErrorEvent, InlineKeyboardButton,
    InlineKeyboardMarkup, LinkPreviewOptions, Message, MessageEntity,
)
from aiogram.utils.token import TokenValidationError
from aiohttp import ClientError, ClientSession, ClientTimeout, web  # Зависимость aiogram.
from telethon import TelegramClient, errors, functions, types, utils
from telethon.sessions import MemorySession, Session, SQLiteSession, StringSession


# 2. Конфиг. Для размещения на GitHub оставляй значения ключей пустыми.
API_ID = os.getenv("API_ID", "0").strip()
API_HASH = os.getenv("API_HASH", "").strip()
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
TELETHON_SESSION = os.getenv("TELETHON_SESSION", "").strip()
# OWNER_ID ограничивает подключение к Render. Готовая локальная сессия определит владельца сама.
OWNER_ID = os.getenv("OWNER_ID", "0").strip()
PUBLIC_BASE_URL = (os.getenv("PUBLIC_BASE_URL") or os.getenv("RENDER_EXTERNAL_URL", "")).strip().rstrip("/")

BOT_NAME = "acczHELP"
PREMIUM_EMOJI = {
    "status": "5355260752762518003",
    "start": "5361930420361378687",
    "content": "5361740436778009413",
    "login": "5348079125061975628",
    "delay": "5361933723191231306",
}
TRY_EMOJI_IN_BUTTONS = os.getenv("TRY_EMOJI_IN_BUTTONS", "false").lower() in {
    "1", "true", "yes",
}
# None включает встроенный баннер. Пустая строка отключает картинку.
# Непустая строка задаёт URL или file_id для этого бота.
START_BANNER_URL = os.getenv("START_BANNER_URL", None)
DATA_DIR = Path(os.getenv("DATA_DIR") or Path(__file__).resolve().parent).resolve()
DB_PATH = DATA_DIR / "data.db"
SESSION_PATH = DATA_DIR / "user_session.session"
PORT = os.getenv("PORT", "").strip()
RPC_TIMEOUT = 90
MIN_DELAY, DEFAULT_DELAY, MAX_DELAY = 3.1, 4.0, 3600.0
DEFAULT_REPORT_MINUTES, MAX_REPORT_MINUTES = 5, 1440
PAGE_SIZE = 8
LIVE_REFRESH = 4
READY_INTERVAL = 45
PAIR_TTL = 600
FLOOD_ERRORS = (
    errors.FloodWaitError, errors.FloodPremiumWaitError, errors.SlowModeWaitError,
    errors.FloodTestPhoneWaitError,
)
AUTH_ERRORS = (errors.UnauthorizedError, errors.AuthKeyError)
LOG = logging.getLogger(BOT_NAME)

# 3. SQLite и модели данных
@dataclass(frozen=True)
class CustomEmoji:
    offset: int
    length: int
    document_id: int


@dataclass(frozen=True)
class Content:
    photo_file_id: str | None
    text: str
    emoji: tuple[CustomEmoji, ...]
    formatting: tuple[MessageEntity, ...] = ()


@dataclass(frozen=True)
class Group:
    peer_id: int
    title: str
    username: str | None
    peer: types.TypeInputPeer | None = None

    def stored(self) -> tuple[int, str, str | None]:
        return self.peer_id, self.title, self.username


@dataclass(frozen=True)
class Pairing:
    token: str
    owner_id: int
    expires_at: float


def content_fields(content: Content) -> tuple[str | None, str, str, str]:
    return (
        content.photo_file_id, content.text,
        json.dumps([asdict(emoji) for emoji in content.emoji]),
        json.dumps([entity.model_dump(mode="json", exclude_none=True) for entity in content.formatting]),
    )


def read_content(row: sqlite3.Row | None) -> Content | None:
    if row is None:
        return None
    return Content(
        row["photo_file_id"], row["text"],
        tuple(CustomEmoji(**item) for item in json.loads(row["content_emoji_ids"])),
        tuple(MessageEntity.model_validate(item) for item in json.loads(row["formatting"])),
    )


def init_db(path: Path = DB_PATH) -> sqlite3.Connection:
    db = sqlite3.connect(path, timeout=5)
    db.row_factory = sqlite3.Row
    try:
        db.executescript("""
            PRAGMA journal_mode = WAL;
            PRAGMA foreign_keys = ON;
            CREATE TABLE IF NOT EXISTS profiles (
                account_id INTEGER PRIMARY KEY,
                delay REAL NOT NULL CHECK (delay >= 3.1),
                report_minutes INTEGER NOT NULL CHECK (report_minutes >= 1),
                next_send_at REAL NOT NULL DEFAULT 0,
                flood_until REAL NOT NULL DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS content (
                account_id INTEGER PRIMARY KEY REFERENCES profiles(account_id),
                photo_file_id TEXT,
                text TEXT NOT NULL,
                content_emoji_ids TEXT NOT NULL,
                formatting TEXT NOT NULL DEFAULT '[]',
                CHECK (photo_file_id IS NOT NULL OR length(text) > 0)
            );
            CREATE TABLE IF NOT EXISTS selected_groups (
                account_id INTEGER NOT NULL REFERENCES profiles(account_id),
                peer_id INTEGER NOT NULL,
                title TEXT NOT NULL,
                username TEXT,
                PRIMARY KEY (account_id, peer_id)
            );
            CREATE TABLE IF NOT EXISTS runs (
                id INTEGER PRIMARY KEY,
                account_id INTEGER NOT NULL REFERENCES profiles(account_id),
                chat_id INTEGER NOT NULL,
                total INTEGER NOT NULL CHECK (total > 0),
                sent INTEGER NOT NULL DEFAULT 0,
                errors INTEGER NOT NULL DEFAULT 0,
                state TEXT NOT NULL DEFAULT 'running',
                note TEXT NOT NULL DEFAULT '',
                stop_requested INTEGER NOT NULL DEFAULT 0,
                CHECK (sent >= 0 AND errors >= 0 AND sent + errors <= total)
            );
            CREATE UNIQUE INDEX IF NOT EXISTS one_running_run
            ON runs(account_id) WHERE state = 'running';
            CREATE TABLE IF NOT EXISTS run_posts (
                run_id INTEGER PRIMARY KEY REFERENCES runs(id) ON DELETE CASCADE,
                kind TEXT NOT NULL,
                source_run_id INTEGER REFERENCES runs(id),
                photo_file_id TEXT,
                text TEXT NOT NULL,
                content_emoji_ids TEXT NOT NULL,
                formatting TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS run_targets (
                id INTEGER PRIMARY KEY,
                run_id INTEGER NOT NULL REFERENCES runs(id) ON DELETE CASCADE,
                peer_id INTEGER NOT NULL,
                title TEXT NOT NULL,
                username TEXT,
                state TEXT NOT NULL DEFAULT 'pending'
                    CHECK (state IN ('pending', 'sending', 'sent', 'failed', 'uncertain')),
                detail TEXT NOT NULL DEFAULT '',
                message_id INTEGER,
                retry_of INTEGER UNIQUE REFERENCES run_targets(id),
                UNIQUE (run_id, peer_id)
            );
            CREATE INDEX IF NOT EXISTS targets_by_state ON run_targets(run_id, state, id);
            CREATE TABLE IF NOT EXISTS group_sets (
                id INTEGER PRIMARY KEY,
                account_id INTEGER NOT NULL REFERENCES profiles(account_id),
                name TEXT NOT NULL,
                name_key TEXT NOT NULL,
                groups_json TEXT NOT NULL,
                UNIQUE (account_id, name_key)
            );
        """)
        # Сохраняем данные пользователей первой версии при обновлении схемы.
        for table, column, definition in (
            ("content", "formatting", "TEXT NOT NULL DEFAULT '[]'"),
            ("runs", "stop_requested", "INTEGER NOT NULL DEFAULT 0"),
        ):
            if column not in {row["name"] for row in db.execute(f"PRAGMA table_info({table})")}:
                db.execute(f"ALTER TABLE {table} ADD COLUMN {column} {definition}")
    except BaseException:
        db.close()
        raise
    return db


class Store:
    RUN_SELECT = """
        SELECT r.*, p.kind, p.source_run_id FROM runs AS r
        LEFT JOIN run_posts AS p ON p.run_id = r.id
    """

    def __init__(self, db: sqlite3.Connection):
        self.db = db

    def ensure_profile(self, account_id: int) -> None:
        with self.db:
            self.db.execute(
                "INSERT OR IGNORE INTO profiles(account_id, delay, report_minutes) VALUES (?, ?, ?)",
                (account_id, DEFAULT_DELAY, DEFAULT_REPORT_MINUTES),
            )

    def profile(self, account_id: int) -> sqlite3.Row:
        return self.db.execute(
            "SELECT * FROM profiles WHERE account_id = ?", (account_id,),
        ).fetchone()

    def set_intervals(
        self, account_id: int, *, delay: float | None = None, minutes: int | None = None,
    ) -> None:
        with self.db:
            self.db.execute(
                """UPDATE profiles SET delay = COALESCE(?, delay),
                   report_minutes = COALESCE(?, report_minutes) WHERE account_id = ?""",
                (delay, minutes, account_id),
            )

    def defer(
        self, account_id: int, until: float, *, flood: bool = False,
        rejected_target: int | None = None,
    ) -> None:
        with self.db:
            self.db.execute(
                """UPDATE profiles SET next_send_at = MAX(next_send_at, ?),
                   flood_until = MAX(flood_until, ?) WHERE account_id = ?""",
                (until, until if flood else 0, account_id),
            )
            if rejected_target is not None:
                # При FloodWait Telegram явно отказал. Группа снова ожидает отправки.
                self.db.execute(
                    "UPDATE run_targets SET state = 'pending' WHERE id = ? AND state = 'sending'",
                    (rejected_target,),
                )

    def save_content(self, account_id: int, content: Content) -> None:
        with self.db:
            self.db.execute(
                """INSERT INTO content(account_id, photo_file_id, text, content_emoji_ids, formatting)
                   VALUES (?, ?, ?, ?, ?)
                   ON CONFLICT(account_id) DO UPDATE SET photo_file_id = excluded.photo_file_id,
                   text = excluded.text, content_emoji_ids = excluded.content_emoji_ids,
                   formatting = excluded.formatting""",
                (account_id, *content_fields(content)),
            )

    def load_content(self, account_id: int) -> Content | None:
        row = self.db.execute(
            "SELECT * FROM content WHERE account_id = ?", (account_id,),
        ).fetchone()
        return read_content(row)

    def groups(self, account_id: int) -> dict[int, Group]:
        rows = self.db.execute(
            "SELECT peer_id, title, username FROM selected_groups WHERE account_id = ? ORDER BY rowid",
            (account_id,),
        )
        return {row["peer_id"]: Group(*row) for row in rows}

    def select_group(self, account_id: int, group: Group) -> None:
        with self.db:
            self.db.execute(
                """INSERT INTO selected_groups VALUES (?, ?, ?, ?)
                   ON CONFLICT(account_id, peer_id) DO UPDATE
                   SET title = excluded.title, username = excluded.username""",
                (account_id, *group.stored()),
            )

    def unselect_group(self, account_id: int, peer_id: int) -> None:
        with self.db:
            self.db.execute(
                "DELETE FROM selected_groups WHERE account_id = ? AND peer_id = ?",
                (account_id, peer_id),
            )

    def sets(self, account_id: int, offset: int) -> list[sqlite3.Row]:
        return self.db.execute(
            "SELECT * FROM group_sets WHERE account_id = ? ORDER BY name_key LIMIT ? OFFSET ?",
            (account_id, PAGE_SIZE + 1, offset),
        ).fetchall()

    def group_set(self, account_id: int, set_id: int) -> sqlite3.Row | None:
        return self.db.execute(
            "SELECT * FROM group_sets WHERE account_id = ? AND id = ?", (account_id, set_id),
        ).fetchone()

    def save_set(self, account_id: int, name: str) -> bool:
        with self.db:
            groups = self.groups(account_id).values()
            if not groups:
                return False
            self.db.execute(
                """INSERT INTO group_sets(account_id, name, name_key, groups_json) VALUES (?, ?, ?, ?)
                   ON CONFLICT(account_id, name_key) DO UPDATE
                   SET name = excluded.name, groups_json = excluded.groups_json""",
                (account_id, name, name.casefold(), json.dumps([group.stored() for group in groups])),
            )
        return True

    def apply_set(self, account_id: int, set_id: int) -> bool:
        with self.db:
            saved = self.group_set(account_id, set_id)
            if saved is None:
                return False
            self.db.execute("DELETE FROM selected_groups WHERE account_id = ?", (account_id,))
            self.db.executemany(
                "INSERT INTO selected_groups VALUES (?, ?, ?, ?)",
                ((account_id, *group) for group in json.loads(saved["groups_json"])),
            )
        return True

    def delete_set(self, account_id: int, set_id: int) -> None:
        with self.db:
            self.db.execute("DELETE FROM group_sets WHERE account_id = ? AND id = ?", (account_id, set_id))

    def recover_runs(self) -> None:
        with self.db:
            self.db.execute(
                """UPDATE run_targets SET state = 'uncertain', detail = ?
                   WHERE state = 'sending' AND run_id IN (SELECT id FROM runs WHERE state = 'running')""",
                ("Запрос прервался. Проверь публикацию в группе.",),
            )
            self.db.execute(
                """UPDATE runs SET state = CASE WHEN stop_requested = 1 THEN 'stopped' ELSE 'interrupted' END,
                   note = CASE WHEN EXISTS (SELECT 1 FROM run_posts WHERE run_id = runs.id)
                       THEN ? ELSE ? END
                   WHERE state = 'running'""",
                (
                    "Процесс перезапустился. Состояние очереди сохранено.",
                    "Запуск прерван. Для старой версии доступны общие счётчики.",
                ),
            )

    def new_run(
        self, account_id: int, chat_id: int, groups: Sequence[Group], content: Content, *,
        kind: str = "bulk", source: int | None = None, retries: dict[int, int] | None = None,
    ) -> int | None:
        if not groups:
            return None
        with self.db:
            cursor = self.db.execute(
                """INSERT INTO runs(account_id, chat_id, total) VALUES (?, ?, ?)
                   ON CONFLICT(account_id) WHERE state = 'running' DO NOTHING""",
                (account_id, chat_id, len(groups)),
            )
            if not cursor.rowcount:
                return None
            run_id = cursor.lastrowid
            self.db.execute(
                "INSERT INTO run_posts VALUES (?, ?, ?, ?, ?, ?, ?)",
                (run_id, kind, source, *content_fields(content)),
            )
            self.db.executemany(
                """INSERT INTO run_targets(run_id, peer_id, title, username, retry_of)
                   VALUES (?, ?, ?, ?, ?)""",
                ((run_id, *group.stored(), (retries or {}).get(group.peer_id)) for group in groups),
            )
        return run_id

    def latest_run(self, account_id: int) -> sqlite3.Row | None:
        return self.db.execute(
            self.RUN_SELECT + "WHERE r.account_id = ? ORDER BY (r.state = 'running') DESC, r.id DESC LIMIT 1",
            (account_id,),
        ).fetchone()

    def run(self, run_id: int, account_id: int | None = None) -> sqlite3.Row | None:
        return self.db.execute(
            self.RUN_SELECT + "WHERE r.id = ? AND (? IS NULL OR r.account_id = ?)",
            (run_id, account_id, account_id),
        ).fetchone()

    def history(self, account_id: int, offset: int) -> list[sqlite3.Row]:
        return self.db.execute(
            self.RUN_SELECT + "WHERE r.account_id = ? ORDER BY r.id DESC LIMIT ? OFFSET ?",
            (account_id, PAGE_SIZE + 1, offset),
        ).fetchall()

    def snapshot(self, run_id: int) -> Content | None:
        return read_content(self.db.execute("SELECT * FROM run_posts WHERE run_id = ?", (run_id,)).fetchone())

    def targets(self, run_id: int, offset: int) -> list[sqlite3.Row]:
        return self.db.execute(
            "SELECT * FROM run_targets WHERE run_id = ? ORDER BY id LIMIT ? OFFSET ?",
            (run_id, PAGE_SIZE + 1, offset),
        ).fetchall()

    def target_count(self, run_id: int, state: str) -> int:
        return self.db.execute(
            "SELECT COUNT(*) FROM run_targets WHERE run_id = ? AND state = ?", (run_id, state),
        ).fetchone()[0]

    def pending(self, run_id: int) -> list[sqlite3.Row]:
        return self.db.execute(
            "SELECT * FROM run_targets WHERE run_id = ? AND state = 'pending' ORDER BY id", (run_id,),
        ).fetchall()

    def retryable(self, run_id: int) -> list[sqlite3.Row]:
        return self.db.execute(
            """SELECT t.* FROM run_targets AS t WHERE t.run_id = ? AND t.state = 'failed'
               AND NOT EXISTS (SELECT 1 FROM run_targets WHERE retry_of = t.id) ORDER BY t.id""",
            (run_id,),
        ).fetchall()

    def interrupted_run(self, account_id: int) -> sqlite3.Row | None:
        return self.db.execute(
            self.RUN_SELECT + """WHERE r.account_id = ? AND r.state = 'interrupted' AND r.stop_requested = 0
               AND p.run_id IS NOT NULL AND EXISTS
                   (SELECT 1 FROM run_targets WHERE run_id = r.id AND state = 'pending')
               ORDER BY r.id DESC LIMIT 1""",
            (account_id,),
        ).fetchone()

    def reopen(self, run_id: int, account_id: int, chat_id: int) -> bool:
        with self.db:
            cursor = self.db.execute(
                """UPDATE runs SET state = 'running', note = '', stop_requested = 0, chat_id = ?
                   WHERE id = ? AND account_id = ? AND state IN ('stopped', 'failed', 'interrupted')
                   AND EXISTS (SELECT 1 FROM run_targets WHERE run_id = runs.id AND state = 'pending')
                   AND NOT EXISTS (SELECT 1 FROM runs WHERE account_id = ? AND state = 'running')""",
                (chat_id, run_id, account_id, account_id),
            )
            return bool(cursor.rowcount)

    def request_stop(self, run_id: int) -> None:
        with self.db:
            self.db.execute("UPDATE runs SET stop_requested = 1 WHERE id = ? AND state = 'running'", (run_id,))

    def begin_target(self, target_id: int) -> None:
        with self.db:
            cursor = self.db.execute(
                "UPDATE run_targets SET state = 'sending' WHERE id = ? AND state = 'pending'", (target_id,),
            )
            if not cursor.rowcount:
                raise RunFailed("Не удалось зафиксировать начало отправки.")

    def target_sending(self, target_id: int) -> bool:
        row = self.db.execute("SELECT state FROM run_targets WHERE id = ?", (target_id,)).fetchone()
        return row is not None and row["state"] == "sending"

    def record(
        self, run_id: int, target_id: int, state: str, detail: str = "", message_id: int | None = None,
    ) -> None:
        with self.db:
            cursor = self.db.execute(
                """UPDATE run_targets SET state = ?, detail = ?, message_id = ?
                   WHERE run_id = ? AND id = ? AND state IN ('pending', 'sending')""",
                (state, detail, message_id, run_id, target_id),
            )
            if cursor.rowcount:
                self.db.execute(
                    "UPDATE runs SET sent = sent + ?, errors = errors + ? WHERE id = ?",
                    (int(state == "sent"), int(state == "failed"), run_id),
                )

    def finish(self, run_id: int, state: str, note: str) -> None:
        with self.db:
            self.db.execute(
                """UPDATE run_targets SET state = 'uncertain', detail = ?
                   WHERE run_id = ? AND state = 'sending'""",
                ("Запрос прервался. Проверь публикацию в группе.", run_id),
            )
            self.db.execute(
                "UPDATE runs SET state = ?, note = ? WHERE id = ?", (state, note, run_id),
            )


# 4. Инициализация aiogram и FSM
dp = Dispatcher(storage=MemoryStorage(), events_isolation=SimpleEventIsolation())


def make_bot() -> Bot:
    return Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))


class Flow(StatesGroup):
    login = State()
    login_code = State()
    login_password = State()
    content = State()
    groups = State()
    manual_group = State()
    group_search = State()
    set_name = State()
    confirm = State()
    test_confirm = State()
    retry_confirm = State()
    delay = State()
    report = State()


# 5. Инициализация MTProto и состояние процесса
def install_session(source: Session) -> SQLiteSession:
    if not source.auth_key or not source.server_address or not source.port:
        raise ValueError("Отсутствуют данные авторизованной сессии.")
    # Сохраняем новый ключ атомарно с отдельным кэшем групп.
    with tempfile.TemporaryDirectory(dir=DATA_DIR) as directory:
        path = Path(directory) / SESSION_PATH.name
        replacement = SQLiteSession(str(path))
        try:
            replacement.set_dc(source.dc_id, source.server_address, source.port)
            replacement.auth_key = source.auth_key
            replacement.save()
        finally:
            replacement.close()
        os.replace(path, SESSION_PATH)
    return SQLiteSession(str(SESSION_PATH))


def open_session(*, local_session: bool) -> SQLiteSession:
    current = SQLiteSession(str(SESSION_PATH))
    # Старый env поддерживается для первичного импорта. Записанный ключ имеет приоритет.
    if local_session or current.auth_key or not TELETHON_SESSION:
        return current
    current.close()
    try:
        source = StringSession(TELETHON_SESSION)
        if source.auth_key is None:
            raise ValueError
    except Exception:
        raise SystemExit("Некорректный TELETHON_SESSION. Повтори --export-session локально.") from None

    return install_session(source)


def make_client(*, local_session: bool = False, session: Session | None = None) -> TelegramClient:
    if session is None:
        session = open_session(local_session=local_session)
    return TelegramClient(
        session, int(API_ID), API_HASH, device_model=BOT_NAME,
        timeout=12, connection_retries=3, request_retries=3 if local_session else 0,
        raise_last_call_error=True, flood_sleep_threshold=0, receive_updates=False,
    )


class Runtime:
    def __init__(self, bot: Bot, client: TelegramClient, store: Store):
        self.bot = bot
        self.client = client
        self.store = store
        self.me: types.User | None = None
        self.account_id: int | None = None
        self.owner_id = int(OWNER_ID or "0")
        self.screen: Message | None = None
        self.preview: Message | None = None
        self.menu_emoji: dict[str, str] = {}
        self.groups: dict[int, Group] = {}
        self.task: asyncio.Task | None = None
        self.run_id: int | None = None
        self.stop = asyncio.Event()
        self.last_report = 0.0
        self.current_group: str | None = None
        self.live_run_id: int | None = None
        self.live_text = ""
        self.last_live_edit = 0.0
        self.live_lock = asyncio.Lock()
        self.ready = False
        self.readiness_checked_at = 0.0
        self.pairing: Pairing | None = None
        self.login_lock = asyncio.Lock()
        self.login_wait_until = 0.0

    def allows(self, user_id: int) -> bool:
        return not self.owner_id or self.owner_id == user_id

    @property
    def active(self) -> bool:
        return self.task is not None and not self.task.done()

    async def check_login(self) -> None:
        async with self.login_lock:
            try:
                if not self.client.is_connected():
                    await self.client.connect()
                me = await self.client.get_me()
            except AUTH_ERRORS:
                me = None
            self.set_login(me)

    def set_login(self, me: object) -> None:
        self.me = me if isinstance(me, types.User) and not me.bot else None
        if self.me:
            if self.account_id != self.me.id:
                self.groups.clear()
            self.account_id = self.me.id
            self.owner_id = int(OWNER_ID or "0") or self.me.id
            self.store.ensure_profile(self.me.id)

    def issue_pairing(self, owner_id: int) -> Pairing:
        now = time.monotonic()
        current = self.pairing
        if current is None or current.expires_at <= now or current.owner_id != owner_id:
            current = Pairing(secrets.token_urlsafe(24), owner_id, now + PAIR_TTL)
            self.pairing = current
        return current


# 6. Меню, custom emoji, группы и экраны
MENU = (
    ("status", "status", "📊", "Статус рассылки", "Статус"),
    ("start", "start_mailing", "🚀", "Начать рассылку", "Запуск"),
    ("content", "set_content", "🖼", "Фото + текст", "Контент"),
    ("login", "login", "🔐", "Вход в аккаунт", "Аккаунт"),
    ("delay", "set_delay", "⏱", "Задержка рассылки", "Интервал"),
)


def button(
    text: str, action: str, *, style: str | None = None, emoji: str | None = None,
) -> InlineKeyboardButton:
    return InlineKeyboardButton(
        text=text, callback_data=action, style=style, icon_custom_emoji_id=emoji,
    )


def keyboard(*rows: list[InlineKeyboardButton]) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=list(rows))


def build_menu_kb(available: dict[str, str] | None = None) -> InlineKeyboardMarkup:
    rows = []
    for key, action, ordinary, label, _ in MENU:
        document_id = PREMIUM_EMOJI[key]
        use_custom = TRY_EMOJI_IN_BUTTONS and document_id in (available or {})
        rows.append([button(
            label if use_custom else f"{ordinary} {label}", action,
            emoji=document_id if use_custom else None,
        )])
    return keyboard(*rows)


async def lookup_emoji(bot: Bot, ids: Sequence[str], *, retry: bool = True) -> dict[str, str]:
    unique = list(dict.fromkeys(ids))
    result = {}
    # Bot API принимает не более 200 идентификаторов за один запрос.
    for offset in range(0, len(unique), 200):
        batch = unique[offset:offset + 200]
        try:
            stickers = await bot.get_custom_emoji_stickers(custom_emoji_ids=batch)
        except TelegramRetryAfter as exc:
            if not retry:
                raise
            await asyncio.sleep(exc.retry_after + 1)
            stickers = await bot.get_custom_emoji_stickers(custom_emoji_ids=batch)
        for sticker in stickers:
            if sticker.custom_emoji_id:
                result[sticker.custom_emoji_id] = sticker.emoji or ""
    missing = set(unique) - result.keys()
    if missing:
        LOG.warning("Недоступные custom emoji: %s", ", ".join(sorted(missing)))
    return result


def parse_custom_emoji(text: str, entities: Sequence[MessageEntity]) -> tuple[CustomEmoji, ...]:
    # И Bot API, и MTProto считают смещения в 16-битных кодовых единицах.
    ends = {0}
    position = 0
    for character in text:
        position += 2 if ord(character) > 0xFFFF else 1
        ends.add(position)
    result = []
    last_end = 0
    for entity in sorted(entities, key=lambda item: item.offset):
        if entity.type != MessageEntityType.CUSTOM_EMOJI:
            continue
        value = entity.custom_emoji_id or ""
        end = entity.offset + entity.length
        if (
            not re.fullmatch(r"[1-9][0-9]{0,18}", value)
            or entity.offset not in ends or end not in ends
            or entity.length <= 0 or entity.offset < last_end
            or int(value) >= 2**63
        ):
            LOG.warning("Некорректная сущность custom emoji в контенте")
            continue
        result.append(CustomEmoji(entity.offset, entity.length, int(value)))
        last_end = end
    return tuple(result)


SIMPLE_FORMATTING = {
    MessageEntityType.BOLD: types.MessageEntityBold,
    MessageEntityType.ITALIC: types.MessageEntityItalic,
    MessageEntityType.UNDERLINE: types.MessageEntityUnderline,
    MessageEntityType.STRIKETHROUGH: types.MessageEntityStrike,
    MessageEntityType.SPOILER: types.MessageEntitySpoiler,
    MessageEntityType.CODE: types.MessageEntityCode,
    MessageEntityType.URL: types.MessageEntityUrl,
}
EXTRA_FORMATTING = {
    MessageEntityType.PRE, MessageEntityType.TEXT_LINK,
    MessageEntityType.BLOCKQUOTE, MessageEntityType.EXPANDABLE_BLOCKQUOTE,
}


def parse_formatting(entities: Sequence[MessageEntity]) -> tuple[MessageEntity, ...]:
    return tuple(
        entity for entity in entities
        if (entity.type in SIMPLE_FORMATTING or entity.type in EXTRA_FORMATTING)
        and (entity.type != MessageEntityType.TEXT_LINK or entity.url)
    )


def mtproto_formatting(content: Content) -> list[types.TypeMessageEntity]:
    result = []
    for entity in content.formatting:
        span = (entity.offset, entity.length)
        if entity.type in SIMPLE_FORMATTING:
            result.append(SIMPLE_FORMATTING[entity.type](*span))
        elif entity.type == MessageEntityType.TEXT_LINK and entity.url:
            result.append(types.MessageEntityTextUrl(*span, entity.url))
        elif entity.type == MessageEntityType.PRE:
            result.append(types.MessageEntityPre(*span, entity.language or ""))
        elif entity.type in {MessageEntityType.BLOCKQUOTE, MessageEntityType.EXPANDABLE_BLOCKQUOTE}:
            result.append(types.MessageEntityBlockquote(
                *span, collapsed=entity.type == MessageEntityType.EXPANDABLE_BLOCKQUOTE,
            ))
    return result


async def delete_message(message: Message) -> None:
    try:
        await message.delete()
    except TelegramAPIError as exc:
        LOG.debug("Удаление сообщения %s: %s", message.message_id, type(exc).__name__)


async def remove_preview(app: Runtime, chat_id: int) -> None:
    if app.preview and app.preview.chat.id == chat_id:
        preview = app.preview
        app.preview = None
        await delete_message(preview)


async def remove_screen(app: Runtime, chat_id: int) -> None:
    if app.screen and app.screen.chat.id == chat_id:
        old = app.screen
        app.screen = None
        app.live_run_id = None
        await delete_message(old)
    await remove_preview(app, chat_id)


async def show(
    app: Runtime, chat_id: int, text: str, markup: InlineKeyboardMarkup | None = None,
    *, image: str | BufferedInputFile | None = None,
) -> Message:
    if image:
        msg = await app.bot.send_photo(chat_id, image, caption=text, reply_markup=markup)
    else:
        msg = await app.bot.send_message(chat_id, text, reply_markup=markup)
    if chat_id == app.owner_id:
        app.screen = msg
        app.live_run_id = None
    return msg


async def render_menu(app: Runtime, chat_id: int) -> None:
    rich = app.menu_emoji
    banner = START_BANNER_URL
    if banner is None:
        banner = BufferedInputFile(base64.b64decode(BANNER_JPEG_B64), "acczHELP.jpg")

    async def send(image: str | BufferedInputFile | None) -> None:
        for available in (rich, {}) if rich else ({},):
            legend = []
            for key, _, ordinary, _, label in MENU:
                document_id = PREMIUM_EMOJI[key]
                if document_id in available:
                    alt = html.escape(available[document_id] or ordinary)
                    icon = f'<tg-emoji emoji-id="{document_id}">{alt}</tg-emoji>'
                else:
                    icon = ordinary
                legend.append(f"{icon} {label}")
            text = (
                "<b>acczHELP</b>\nУправляй рассылкой в группы.\n\n"
                + "  ·  ".join(legend[:3]) + "\n" + "  ·  ".join(legend[3:])
            )
            if app.me is None:
                text += "\n\nПодключи аккаунт перед отправкой."
            try:
                await show(app, chat_id, text, build_menu_kb(available), image=image)
                return
            except TelegramBadRequest:
                if not available:
                    raise
                LOG.info("Меню с custom emoji отклонено. Используются обычные эмодзи.")

    try:
        await send(banner or None)
    except TelegramBadRequest:
        if not banner:
            raise
        LOG.warning("Баннер отклонён Bot API. Меню отправлено текстом.")
        await send(None)


def as_group(entity: object) -> Group | None:
    if isinstance(entity, types.Chat):
        allowed = not (entity.left or entity.deactivated or entity.migrated_to)
    elif isinstance(entity, types.Channel):
        allowed = bool(entity.megagroup and not entity.left and not entity.min and entity.access_hash)
    else:
        return None
    if not allowed:
        return None
    return Group(
        utils.get_peer_id(entity), " ".join(entity.title.split()) or "Группа",
        getattr(entity, "username", None), utils.get_input_peer(entity),
    )


async def refresh_groups(app: Runtime) -> None:
    groups = {}
    async for dialog in app.client.iter_dialogs():
        group = as_group(dialog.entity)
        if group:
            groups[group.peer_id] = group
    app.groups = groups


async def resolve_group(app: Runtime, query: str) -> Group | None:
    if re.fullmatch(r"-?[0-9]{1,19}", query):
        number = int(query)
        direct = app.groups.get(number)
        if direct:
            return direct
        if number > 0:
            matches = [group for group in app.groups.values() if utils.resolve_id(group.peer_id)[0] == number]
            if len(matches) > 1:
                raise ValueError("Найдено несколько групп. Укажи ID со знаком минус.")
            return matches[0] if matches else None
        entity = await app.client.get_entity(number)
    elif re.fullmatch(r"@[A-Za-z0-9_]{1,32}", query):
        entity = await app.client.get_entity(query)
    else:
        raise ValueError("Укажи @username группы или числовой ID.")
    return as_group(entity)


def back_menu() -> list[InlineKeyboardButton]:
    return [button("← В меню", "menu")]


def page_nav(page: int, more: bool, prefix: str) -> list[InlineKeyboardButton]:
    nav = []
    if page > 0:
        nav.append(button("‹ Назад", f"{prefix}:{page - 1}"))
    if more:
        nav.append(button("Далее ›", f"{prefix}:{page + 1}"))
    return nav


async def show_groups(
    app: Runtime, chat_id: int, account_id: int, state: FSMContext, page: int = 0,
) -> None:
    data = await state.get_data()
    testing = data.get("testing", False)
    selected_only = data.get("selected_only", False) and not testing
    query = data.get("group_query", "")
    needle = query.casefold().removeprefix("@")
    selected = app.store.groups(account_id)
    pool = app.groups if testing else {**selected, **app.groups}
    groups = sorted(
        (
            group for group in pool.values()
            if (not selected_only or group.peer_id in selected)
            and any(needle in value.casefold() for value in (
                group.title, group.username or "", str(group.peer_id),
            ))
        ),
        key=lambda group: (group.title.casefold(), group.peer_id),
    )
    pages = max(1, (len(groups) + PAGE_SIZE - 1) // PAGE_SIZE)
    page = min(max(0, page), pages - 1)
    rows = []
    for group in groups[page * PAGE_SIZE:(page + 1) * PAGE_SIZE]:
        if testing:
            rows.append([button(group.title[:50], f"g:test:{group.peer_id}")])
            continue
        mark = "✅" if group.peer_id in selected else "⬜"
        suffix = " · вне списка" if group.peer_id not in app.groups else ""
        rows.append([button(f"{mark} {group.title[:43]}{suffix}", f"g:t:{page}:{group.peer_id}")])
    nav = page_nav(page, page + 1 < pages, "g:p")
    if nav:
        rows.append(nav)
    search = [button("🔎 Поиск", "g:search")]
    if query:
        search.append(button("Сбросить поиск", "g:clear"))
    rows.append(search)
    if testing:
        rows.extend([[button("← К предпросмотру", "g:done")], back_menu()])
        text = "<b>Тестовая группа</b>\nВыбери одну группу для пробной отправки."
    else:
        rows.extend([
            [button("Все группы" if selected_only else "✅ Выбранные", "g:filter"),
             button("📁 Наборы", "g:sets:0")],
            [button("➕ Добавить группу", "g:manual"), button("↻ Обновить", "g:refresh")],
            [button("Готово", "g:done", style="primary")],
            back_menu(),
        ])
        view = " · только выбранные" if selected_only else ""
        text = f"<b>Выбор групп</b>\nВыбрано <b>{len(selected)}</b>{view}"
    if query:
        text += f"\nПоиск «{html.escape(query)}»"
    text += f"\nСтраница {page + 1} из {pages}"
    if not groups:
        text += "\n\nПодходящих групп нет."
    await show(app, chat_id, text, keyboard(*rows))


async def show_sets(app: Runtime, chat_id: int, account_id: int, page: int) -> None:
    sets = app.store.sets(account_id, page * PAGE_SIZE)
    rows = [[button(item["name"], f"g:set:{item['id']}")] for item in sets[:PAGE_SIZE]]
    nav = page_nav(page, len(sets) > PAGE_SIZE, "g:sets")
    if nav:
        rows.append(nav)
    rows.extend([
        [button("💾 Сохранить выбранные группы", "g:save_set")],
        [button("← К группам", "g:p:0")], back_menu(),
    ])
    text = "<b>Наборы групп</b>"
    if not sets:
        text += "\nСохрани текущий выбор, чтобы использовать его снова."
    await show(app, chat_id, text, keyboard(*rows))


async def show_set(
    app: Runtime, chat_id: int, account_id: int, set_id: int, *, deleting: bool = False,
) -> None:
    saved = app.store.group_set(account_id, set_id)
    if saved is None:
        await show_sets(app, chat_id, account_id, 0)
        return
    groups = json.loads(saved["groups_json"])
    title = html.escape(saved["name"])
    if deleting:
        text = f"<b>Удалить набор «{title}»?</b>"
        rows = [[button("Удалить набор", f"g:delete_go:{set_id}", style="danger")]]
    else:
        text = f"<b>{title}</b>\nГрупп в наборе <b>{len(groups)}</b>\nПрименение заменит текущий выбор."
        rows = [
            [button("Применить набор", f"g:apply:{set_id}", style="primary")],
            [button("Удалить набор", f"g:delete:{set_id}")],
        ]
    await show(app, chat_id, text, keyboard(*rows, [button("← К наборам", "g:sets:0")], back_menu()))


async def show_settings(app: Runtime, chat_id: int, account_id: int) -> None:
    profile = app.store.profile(account_id)
    await show(
        app, chat_id,
        f"<b>Интервалы</b>\n"
        f"Задержка {profile['delay']:g} сек\nОтчёт каждые {profile['report_minutes']} мин",
        keyboard(
            [button("⏱ Задержка отправки", "pace:send")],
            [button("📊 Интервал отчётов", "pace:report")],
            back_menu(),
        ),
    )


RUN_STATES = {
    "running": "🟢 Рассылка идёт",
    "done": "✅ Рассылка завершена",
    "stopped": "⏹ Рассылка остановлена",
    "interrupted": "⏸ Рассылка прервана",
    "failed": "⚠️ Рассылка завершилась с ошибкой",
}
TARGET_STATES = {
    "pending": "Ожидает отправки",
    "sending": "Отправляется",
    "sent": "Отправлено",
    "failed": "Ошибка отправки",
    "uncertain": "Доставка не подтверждена",
}


def run_name(run: sqlite3.Row) -> str:
    name = {"test": "Тестовая отправка", "retry": "Повтор"}.get(run["kind"], "Рассылка")
    return f"{name} #{run['id']}"


def status_text(app: Runtime, account_id: int, run: sqlite3.Row | None) -> str:
    profile = app.store.profile(account_id)
    intervals = f"Задержка {profile['delay']:g} сек\nОтчёт каждые {profile['report_minutes']} мин"
    if run is None:
        return "<b>Статус рассылки</b>\nРассылок пока нет.\n\n" + intervals
    state = RUN_STATES[run["state"]]
    current = ""
    if run["state"] == "running":
        remaining = max(0, int(profile["flood_until"] - time.time() + 0.999))
        if run["stop_requested"]:
            state = "⏹ Останавливаю рассылку"
        elif remaining:
            state = f"⏳ Пауза Telegram ещё {remaining} сек"
        if app.run_id == run["id"] and app.current_group:
            current = f"\nГруппа <b>{html.escape(app.current_group[:120])}</b>"
        elif not remaining and not run["stop_requested"]:
            current = "\nГотовлю пост и проверяю очередь."
    uncertain = app.store.target_count(run["id"], "uncertain")
    processed = run["sent"] + run["errors"] + uncertain
    filled = processed * 10 // run["total"]
    progress = "▰" * filled + "▱" * (10 - filled)
    source = f"\nИсходная рассылка #{run['source_run_id']}" if run["source_run_id"] else ""
    text = (
        f"<b>{run_name(run)}</b>{source}\n{state}{current}\n<code>{progress}</code>\n\n"
        f"Обработано <b>{processed} из {run['total']}</b>\n"
        f"Успешно <b>{run['sent']}</b>\nОшибок <b>{run['errors']}</b>"
    )
    if uncertain:
        text += f"\nДоставка не подтверждена <b>{uncertain}</b>"
    text += f"\n\n{intervals}"
    if run["note"]:
        text += "\n\n" + html.escape(run["note"])
    return text


def status_keyboard(app: Runtime, run: sqlite3.Row | None) -> InlineKeyboardMarkup:
    rows = []
    if run:
        run_id = run["id"]
        if run["state"] == "running":
            if not run["stop_requested"]:
                rows.append([button("⏹ Остановить", f"stop:{run_id}", style="danger")])
            rows.append([button("↻ Обновить статус", f"run:{run_id}")])
        elif app.me and app.store.target_count(run_id, "pending"):
            rows.append([button("▶ Продолжить с ожидающих", f"resume:{run_id}", style="primary")])
        if run["kind"]:
            rows.append([button("📋 Отчёт по группам", f"results:{run_id}:0")])
    rows.append([button("🗂 История запусков", "history:0")])
    rows.append(back_menu())
    return keyboard(*rows)


async def show_status(
    app: Runtime, chat_id: int, account_id: int, run_id: int | None = None,
) -> None:
    run = app.store.run(run_id, account_id) if run_id is not None else app.store.latest_run(account_id)
    text = status_text(app, account_id, run)
    await show(app, chat_id, text, status_keyboard(app, run))
    if run and run["state"] == "running":
        app.live_run_id = run["id"]
        app.live_text = text
        app.last_live_edit = time.monotonic()


async def show_history(app: Runtime, chat_id: int, account_id: int, page: int) -> None:
    runs = app.store.history(account_id, page * PAGE_SIZE)
    rows = [[button(f"{run_name(run)} · {RUN_STATES[run['state']].split(' ', 1)[0]}",
                    f"run:{run['id']}")] for run in runs[:PAGE_SIZE]]
    nav = page_nav(page, len(runs) > PAGE_SIZE, "history")
    if nav:
        rows.append(nav)
    rows.extend([[button("← К статусу", "status")], back_menu()])
    text = "<b>История запусков</b>" + ("" if runs else "\nЗапусков пока нет.")
    await show(app, chat_id, text, keyboard(*rows))


async def show_results(app: Runtime, chat_id: int, account_id: int, run_id: int, page: int) -> None:
    run = app.store.run(run_id, account_id)
    if run is None:
        await show_status(app, chat_id, account_id)
        return
    targets = app.store.targets(run_id, page * PAGE_SIZE)
    lines = [f"<b>Отчёт по группам · {run_name(run)}</b>"]
    for target in targets[:PAGE_SIZE]:
        lines.append(f"\n<b>{html.escape(target['title'][:100])}</b>\n{TARGET_STATES[target['state']]}")
        if target["detail"]:
            lines.append(html.escape(target["detail"][:150]))
    if not targets:
        lines.append("Для этого запуска доступны общие счётчики.")
    rows = []
    nav = page_nav(page, len(targets) > PAGE_SIZE, f"results:{run_id}")
    if nav:
        rows.append(nav)
    if app.me and run["state"] != "running" and app.store.retryable(run_id):
        rows.append([button("↻ Повторить подтверждённые ошибки", f"retry:{run_id}", style="primary")])
    rows.extend([[button("← К статусу", f"run:{run_id}")], back_menu()])
    await show(app, chat_id, "\n".join(lines), keyboard(*rows))


async def show_login(app: Runtime, chat_id: int, state: FSMContext) -> None:
    if app.me:
        await state.clear()
        identity = f"@{app.me.username}" if app.me.username else app.me.first_name or str(app.me.id)
        await show(
            app, chat_id, f"<b>Аккаунт подключён</b>\n{html.escape(identity)}",
            keyboard(back_menu()),
        )
        return
    await state.clear()
    if not app.owner_id:
        await show(
            app, chat_id,
            f"<b>🔐 Вход в аккаунт</b>\n\nТвой Telegram ID <code>{chat_id}</code>. "
            "Добавь его как OWNER_ID в Render, затем открой вход снова.",
            keyboard(back_menu()),
        )
        return
    if app.active:
        await show(app, chat_id, "Дождись остановки текущей рассылки.", keyboard(back_menu()))
        return
    await state.set_state(Flow.login)
    await show_auth_step(app, chat_id, state)


async def show_auth_step(
    app: Runtime, chat_id: int, state: FSMContext, *, notice: str = "",
) -> None:
    current = await state.get_state()
    rows = []
    if current == Flow.login_code.state:
        text = "Пришли код из Telegram. Можно ввести через точки, например <code>2.3.4.5.6</code>."
    elif current == Flow.login_password.state:
        dotted = (await state.get_data()).get("password_dotted", False)
        text = "Пришли пароль 2FA." if not dotted else "Пришли пароль 2FA с точками между символами."
        mark = "✅" if dotted else "⬜"
        rows.append([button(f"{mark} Пароль с точками", "login:password_dots")])
    else:
        text = "Пришли номер телефона с кодом страны, например <code>+37412345678</code>."
    if notice:
        text = html.escape(notice) + "\n\n" + text
    await show(app, chat_id, "<b>🔐 Вход в аккаунт</b>\n\n" + text, keyboard(*rows, back_menu()))


async def send_preview(app: Runtime, chat_id: int, account_id: int, content: Content) -> str:
    custom = list(content.emoji)
    note = ""
    if custom:
        try:
            checked = await asyncio.wait_for(
                prepare_emoji(app, account_id, content, bool(app.me and app.me.premium), preview=True),
                timeout=8,
            )
        except (RunFailed, errors.RPCError, OSError, asyncio.TimeoutError):
            note = "Доступность премиум-эмодзи проверится при отправке."
        else:
            custom = [CustomEmoji(item.offset, item.length, item.document_id) for item in checked]
            if len(custom) < len(content.emoji):
                note = f"Обычные эмодзи будут использованы в {len(content.emoji) - len(custom)} местах."

    for use_custom in (True, False) if custom else (False,):
        entities = list(content.formatting)
        if use_custom:
            entities.extend(
                MessageEntity(
                    type=MessageEntityType.CUSTOM_EMOJI, offset=item.offset, length=item.length,
                    custom_emoji_id=str(item.document_id),
                )
                for item in custom
            )
        entities.sort(key=lambda item: (item.offset, -item.length))
        try:
            if content.photo_file_id:
                app.preview = await app.bot.send_photo(
                    chat_id, content.photo_file_id, caption=content.text,
                    caption_entities=entities, parse_mode=None,
                )
            else:
                app.preview = await app.bot.send_message(
                    chat_id, content.text, entities=entities, parse_mode=None,
                    link_preview_options=LinkPreviewOptions(is_disabled=True),
                )
        except TelegramBadRequest:
            if not use_custom:
                raise
            continue
        rendered = app.preview.caption_entities if content.photo_file_id else app.preview.entities
        rendered_count = sum(item.type == MessageEntityType.CUSTOM_EMOJI for item in rendered or ())
        if rendered_count < len(custom):
            note = (note + " В предпросмотре часть эмодзи показана обычными. "
                    "Итог можно проверить пробной отправкой.").strip()
        return note
    return note


async def show_confirmation(app: Runtime, chat_id: int, account_id: int, state: FSMContext) -> None:
    groups = app.store.groups(account_id)
    content = app.store.load_content(account_id)
    await state.update_data(testing=False)
    if content is None:
        await show(
            app, chat_id, "<b>Подготовка рассылки</b>\nСначала сохрани фото или текст.",
            keyboard([button("🖼 Фото + текст", "set_content")], [button("← К группам", "start_mailing")], back_menu()),
        )
        return
    try:
        note = await send_preview(app, chat_id, account_id, content)
    except TelegramBadRequest:
        await show(
            app, chat_id, "Telegram не открыл предпросмотр. Сохрани пост повторно.",
            keyboard([button("🖼 Пересохранить пост", "set_content")], back_menu()),
        )
        return
    await state.set_state(Flow.confirm)
    names = "\n".join(f"• {html.escape(group.title[:100])}" for group in list(groups.values())[:8])
    if len(groups) > 8:
        names += f"\n… и ещё {len(groups) - 8}"
    text = f"<b>Предпросмотр поста</b>\nПост показан выше.\n\nВыбрано групп <b>{len(groups)}</b>"
    if names:
        text += "\n" + names
    if note:
        text += "\n\n" + html.escape(note)
    rows = []
    if groups:
        rows.append([button("🚀 Подтвердить отправку", "confirm", style="primary")])
    await show(
        app, chat_id, text,
        keyboard(
            *rows,
            [button("🧪 Пробная отправка", "test:choose")],
            [button("Группы", "start_mailing"), button("Изменить пост", "set_content")],
            back_menu(),
        ),
    )


# 7. Команды, callback и ввод через FSM
@dp.message(CommandStart(), F.chat.type == ChatType.PRIVATE)
@dp.message(Command("cancel"), F.chat.type == ChatType.PRIVATE)
async def menu_command(message: Message, state: FSMContext, app: Runtime) -> None:
    if message.from_user is None or not app.allows(message.from_user.id):
        await message.answer("Панель доступна владельцу acczHELP.")
        return
    if await state.get_state() == Flow.login_password.state:
        await accept_login_input(message, state, app)
        return
    await state.clear()
    await remove_screen(app, message.chat.id)
    await render_menu(app, message.chat.id)


def remember_flood(
    app: Runtime, account_id: int, exc: errors.RPCError, *, rejected_target: int | None = None,
) -> int:
    seconds = max(1, int(exc.seconds)) + 1
    app.store.defer(
        account_id, time.time() + seconds, flood=True, rejected_target=rejected_target,
    )
    LOG.info("Telegram запросил паузу %s сек (%s)", seconds, type(exc).__name__)
    return seconds


async def update_group_screen(
    app: Runtime, chat_id: int, account_id: int, state: FSMContext,
) -> None:
    await state.set_state(Flow.groups)
    testing = (await state.get_data()).get("testing", False)
    fallback = (
        button("← К предпросмотру", "g:done")
        if testing else button("➕ Добавить группу", "g:manual")
    )
    remaining = app.store.profile(account_id)["flood_until"] - time.time()
    if remaining > 0:
        await show(
            app, chat_id, f"Telegram попросил паузу. Осталось около {int(remaining) + 1} сек.",
            keyboard([button("↻ Обновить группы", "g:refresh"), fallback], back_menu()),
        )
        return
    try:
        await refresh_groups(app)
    except FLOOD_ERRORS as exc:
        seconds = remember_flood(app, account_id, exc)
        hint = f"Telegram попросил паузу на {seconds} сек."
    except AUTH_ERRORS:
        app.me = None
        await show_login(app, chat_id, state)
        return
    except (errors.RPCError, OSError, asyncio.TimeoutError) as exc:
        LOG.warning("Список групп: %s", type(exc).__name__)
        hint = "Список групп сейчас недоступен. Попробуй ещё раз."
    else:
        await show_groups(app, chat_id, account_id, state)
        return
    await show(
        app, chat_id, hint,
        keyboard(
            [button("↻ Обновить", "g:refresh"), fallback],
            back_menu(),
        ),
    )


async def group_action(
    app: Runtime, chat_id: int, account_id: int, state: FSMContext, action: str,
) -> None:
    data = await state.get_data()
    testing = data.get("testing", False)
    if action == "g:refresh":
        await update_group_screen(app, chat_id, account_id, state)
        return
    if action == "g:manual" and not testing:
        await state.set_state(Flow.manual_group)
        await show(
            app, chat_id, "<b>Добавить группу</b>\nПришли её @username или числовой ID.",
            keyboard([button("← К группам", "g:p:0")], back_menu()),
        )
        return
    if action == "g:search":
        await state.set_state(Flow.group_search)
        await show(
            app, chat_id, "<b>Поиск групп</b>\nПришли часть названия, @username или ID.",
            keyboard([button("← К группам", "g:p:0")], back_menu()),
        )
        return
    if action == "g:done":
        await show_confirmation(app, chat_id, account_id, state)
        return
    if testing and (match := re.fullmatch(r"g:test:(-?[0-9]{1,19})", action)):
        group = app.groups.get(int(match[1]))
        if group:
            await state.set_state(Flow.test_confirm)
            await state.update_data(test_peer=group.peer_id)
            await show(
                app, chat_id, f"<b>Подтверди пробную отправку</b>\nГруппа «{html.escape(group.title[:160])}».",
                keyboard(
                    [button("🧪 Отправить в эту группу", "test:send", style="primary")],
                    [button("← К тестовым группам", "g:p:0")], back_menu(),
                ),
            )
            return
    if not testing and await group_set_action(app, chat_id, account_id, state, action):
        return
    page = 0
    if action == "g:clear":
        await state.update_data(group_query="")
    elif action == "g:filter" and not testing:
        await state.update_data(selected_only=not data.get("selected_only", False))
    elif not testing and (match := re.fullmatch(r"g:t:([0-9]{1,8}):(-?[0-9]{1,19})", action)):
        page, peer_id = map(int, match.groups())
        if peer_id in app.store.groups(account_id):
            app.store.unselect_group(account_id, peer_id)
        elif peer_id in app.groups:
            app.store.select_group(account_id, app.groups[peer_id])
    elif match := re.fullmatch(r"g:p:([0-9]{1,8})", action):
        page = int(match[1])
    await state.set_state(Flow.groups)
    await show_groups(app, chat_id, account_id, state, page)


async def group_set_action(
    app: Runtime, chat_id: int, account_id: int, state: FSMContext, action: str,
) -> bool:
    if action == "g:save_set":
        if not app.store.groups(account_id):
            await show(
                app, chat_id, "Выбери группы для нового набора.",
                keyboard([button("← К группам", "g:p:0")], back_menu()),
            )
        else:
            await state.set_state(Flow.set_name)
            await show(
                app, chat_id, "Пришли название набора до 48 символов. Совпадающее имя обновит набор.",
                keyboard([button("← К наборам", "g:sets:0")], back_menu()),
            )
        return True
    match = re.fullmatch(r"g:(sets|set|apply|delete|delete_go):([0-9]{1,18})", action)
    if not match:
        return False
    kind, value = match[1], int(match[2])
    await state.set_state(Flow.groups)
    if kind == "sets":
        await show_sets(app, chat_id, account_id, min(value, 10**7))
    elif kind in {"set", "delete"}:
        await show_set(app, chat_id, account_id, value, deleting=kind == "delete")
    elif kind == "apply":
        if app.store.apply_set(account_id, value):
            await state.update_data(selected_only=True, group_query="")
            await show_groups(app, chat_id, account_id, state)
        else:
            await show_sets(app, chat_id, account_id, 0)
    else:
        app.store.delete_set(account_id, value)
        await show_sets(app, chat_id, account_id, 0)
    return True


async def run_action(
    app: Runtime, chat_id: int, account_id: int, state: FSMContext, action: str,
) -> bool:
    match = re.fullmatch(r"(run|resume|results|history|retry|retry_go):([0-9]{1,18})(?::([0-9]{1,8}))?", action)
    if not match:
        return False
    kind, value, page = match[1], int(match[2]), int(match[3] or "0")
    run = app.store.run(value, account_id) if kind != "history" else None
    if kind == "retry_go":
        current = await state.get_state()
        data = await state.get_data()
        await state.clear()
        if run and current == Flow.retry_confirm.state and data.get("retry_source") == value:
            await launch_retry(app, chat_id, account_id, run)
        else:
            await show_status(app, chat_id, account_id)
        return True

    await state.clear()
    if kind == "history":
        await show_history(app, chat_id, account_id, min(value, 10**7))
    elif run is None or kind == "run":
        await show_status(app, chat_id, account_id, run["id"] if run else None)
    elif kind == "results":
        await show_results(app, chat_id, account_id, value, page)
    elif kind == "resume":
        await resume_run(app, chat_id, account_id, value)
    elif run["state"] != "running" and (targets := app.store.retryable(value)):
        await state.set_state(Flow.retry_confirm)
        await state.update_data(retry_source=value)
        await show(
            app, chat_id,
            f"<b>Повтор отправки #{value}</b>\nБудет отправлен исходный пост. Групп <b>{len(targets)}</b>.",
            keyboard(
                [button("Подтвердить повтор", f"retry_go:{value}", style="primary")],
                [button("← К отчёту", f"results:{value}:0")], back_menu(),
            ),
        )
    else:
        await show_results(app, chat_id, account_id, value, 0)
    return True


@dp.callback_query(F.message.chat.type == ChatType.PRIVATE)
async def navigate(callback: CallbackQuery, state: FSMContext, app: Runtime) -> None:
    message = callback.message
    if not isinstance(message, Message) or not app.allows(callback.from_user.id):
        with suppress(TelegramAPIError):
            await callback.answer("Панель доступна владельцу. Открой /start.", show_alert=True)
        return

    chat_id = message.chat.id
    if app.screen and app.screen.chat.id == chat_id and message.message_id != app.screen.message_id:
        with suppress(TelegramAPIError):
            await callback.answer("Открой последнее сообщение панели.")
        await delete_message(message)
        return
    with suppress(TelegramAPIError):
        await callback.answer()
    app.screen = None
    app.live_run_id = None
    await delete_message(message)
    await remove_preview(app, chat_id)

    action = callback.data or "menu"
    current = await state.get_state()
    if action == "menu":
        await state.clear()
        await render_menu(app, chat_id)
        return
    if action == "login:password_dots" and current == Flow.login_password.state and app.owner_id:
        dotted = (await state.get_data()).get("password_dotted", False)
        await state.update_data(password_dotted=not dotted)
        await show_auth_step(app, chat_id, state)
        return
    read_only = action == "status" or action.startswith(("run:", "results:", "history:"))
    if action in {"login", "login_check"} or (app.me is None and not (read_only and app.account_id)):
        if action == "login_check":
            await app.check_login()
            if not app.allows(callback.from_user.id):
                await state.clear()
                await show(app, chat_id, "Панель доступна владельцу acczHELP.")
                return
        await show_login(app, chat_id, state)
        return

    account_id = app.account_id
    if account_id is None:
        await show_login(app, chat_id, state)
        return
    if action == "status":
        await state.clear()
        await show_status(app, chat_id, account_id)
    elif action.startswith("stop:"):
        if action == f"stop:{app.run_id}":
            app.store.request_stop(app.run_id)
            app.stop.set()
        await state.clear()
        await show_status(app, chat_id, account_id)
    elif action == "set_content":
        await state.set_state(Flow.content)
        await show(
            app, chat_id, "<b>🖼 Фото + текст</b>\n\n"
            "Пришли текст одним сообщением или отправь фото с подписью. "
            "Можно отправить фото без подписи. Премиум-эмодзи вставляй в текст или подпись.",
            keyboard(back_menu()),
        )
    elif action == "set_delay":
        await state.clear()
        await show_settings(app, chat_id, account_id)
    elif action == "pace:send":
        await state.set_state(Flow.delay)
        await show(
            app, chat_id, f"Пришли задержку от {MIN_DELAY:g} до {MAX_DELAY:g} сек. Например, 4.",
            keyboard([button("← К интервалам", "set_delay")], back_menu()),
        )
    elif action == "pace:report":
        await state.set_state(Flow.report)
        await show(
            app, chat_id, f"Пришли интервал отчётов целым числом от 1 до {MAX_REPORT_MINUTES} минут.",
            keyboard([button("← К интервалам", "set_delay")], back_menu()),
        )
    elif action == "start_mailing":
        await state.clear()
        if app.active:
            await show_status(app, chat_id, account_id)
        else:
            await update_group_screen(app, chat_id, account_id, state)
    elif action.startswith("g:") and current in {
        Flow.groups.state, Flow.manual_group.state, Flow.confirm.state, Flow.group_search.state,
        Flow.set_name.state, Flow.test_confirm.state,
    }:
        await group_action(app, chat_id, account_id, state, action)
    elif action == "preview":
        await state.clear()
        await show_confirmation(app, chat_id, account_id, state)
    elif action == "confirm" and current == Flow.confirm.state:
        await state.clear()
        await launch(app, chat_id, account_id)
    elif action == "test:choose" and current == Flow.confirm.state:
        await state.update_data(testing=True, group_query="", selected_only=False)
        await update_group_screen(app, chat_id, account_id, state)
    elif action == "test:send" and current == Flow.test_confirm.state:
        group = app.groups.get((await state.get_data()).get("test_peer"))
        await state.clear()
        if group:
            await launch(app, chat_id, account_id, test_group=group)
        else:
            await show_confirmation(app, chat_id, account_id, state)
    elif await run_action(app, chat_id, account_id, state, action):
        return
    else:
        await state.clear()
        await render_menu(app, chat_id)


async def login_request(app: Runtime, operation: Callable[[], Awaitable[object]]) -> object:
    async with app.login_lock:
        if not app.client.is_connected():
            await asyncio.wait_for(app.client.connect(), timeout=20)
        # При смене дата-центра Telethon уже переключает соединение перед исключением.
        for attempt in range(2):
            try:
                return await asyncio.wait_for(operation(), timeout=30)
            except (errors.PhoneMigrateError, errors.NetworkMigrateError, errors.UserMigrateError):
                if attempt:
                    raise
    raise RuntimeError("Telegram не завершил вход.")


async def finish_login(app: Runtime, chat_id: int, state: FSMContext, me: object) -> None:
    if not isinstance(me, types.User) or me.bot:
        await remove_screen(app, chat_id)
        await show_auth_step(app, chat_id, state, notice="Telegram не подтвердил пользовательский аккаунт.")
        return
    try:
        app.client.session.save()
        app.set_login(me)
    except sqlite3.Error as exc:
        LOG.error("Сохранение сессии: %s", type(exc).__name__)
        await remove_screen(app, chat_id)
        await show_auth_step(app, chat_id, state, notice="Не удалось сохранить сессию. Проверь диск на Render.")
        return
    app.login_wait_until = 0.0
    await state.clear()
    await remove_screen(app, chat_id)
    await show_login(app, chat_id, state)

    # Очередь, прерванная до повторного входа, продолжает ожидающие группы.
    pending = app.store.interrupted_run(me.id)
    if pending and not app.active:
        await remove_screen(app, chat_id)
        await resume_run(app, chat_id, me.id, pending["id"])


async def handle_login_error(
    app: Runtime, chat_id: int, state: FSMContext, exc: Exception,
) -> None:
    name = type(exc).__name__
    if isinstance(exc, FLOOD_ERRORS):
        seconds = max(1, int(exc.seconds)) + 1
        app.login_wait_until = time.monotonic() + seconds
        notice = f"Telegram попросил подождать {seconds} сек."
    elif name in {"PhoneCodeExpiredError", "PhoneCodeHashEmptyError"}:
        await state.clear()
        await state.set_state(Flow.login)
        notice = "Код истёк. Пришли номер ещё раз, чтобы запросить новый."
    elif name in {"PhoneCodeInvalidError", "PhoneCodeEmptyError"}:
        notice = "Telegram не принял код. Проверь цифры и попробуй ещё раз."
    elif name == "PasswordHashInvalidError":
        notice = "Telegram не принял пароль 2FA. Попробуй ещё раз."
    elif name == "PhoneNumberInvalidError":
        notice = "Telegram не принял номер. Проверь код страны и цифры."
    elif name == "PhoneNumberBannedError":
        notice = "Telegram сообщил, что номер заблокирован."
    elif name == "PhoneNumberFloodError":
        notice = "Telegram временно ограничил отправку кодов на этот номер."
    elif name == "ApiIdInvalidError":
        notice = "Проверь API_ID и API_HASH в настройках Render."
    else:
        LOG.warning("Вход MTProto: %s", name)
        notice = "Telegram сейчас недоступен. Попробуй ещё раз."
    await remove_screen(app, chat_id)
    await show_auth_step(app, chat_id, state, notice=notice)


async def accept_login_input(message: Message, state: FSMContext, app: Runtime) -> None:
    # Телефон, код и пароль обрабатываются в памяти и удаляются из чата.
    await delete_message(message)
    if not app.owner_id or message.from_user is None or message.from_user.id != app.owner_id:
        await state.clear()
        await show_login(app, message.chat.id, state)
        return
    current = await state.get_state()
    value = message.text
    if not isinstance(value, str):
        await remove_screen(app, message.chat.id)
        await show_auth_step(app, message.chat.id, state, notice="Пришли данные текстовым сообщением.")
        return
    remaining = app.login_wait_until - time.monotonic()
    if remaining > 0:
        await remove_screen(app, message.chat.id)
        await show_auth_step(app, message.chat.id, state, notice=f"Подожди ещё {int(remaining) + 1} сек.")
        return
    data = await state.get_data()
    try:
        if current == Flow.login.state:
            phone = re.sub(r"[\s()-]", "", value)
            if not re.fullmatch(r"\+[1-9][0-9]{6,14}", phone):
                await remove_screen(app, message.chat.id)
                await show_auth_step(app, message.chat.id, state, notice="Проверь номер и код страны.")
                return
            sent = await login_request(app, lambda: app.client.send_code_request(phone))
            phone_code_hash = getattr(sent, "phone_code_hash", None)
            if not isinstance(phone_code_hash, str) or not phone_code_hash:
                raise ValueError("Telegram не вернул данные кода.")
            await state.set_data({"phone": phone, "phone_code_hash": phone_code_hash})
            await state.set_state(Flow.login_code)
            await remove_screen(app, message.chat.id)
            await show_auth_step(app, message.chat.id, state)
            return

        if current == Flow.login_code.state:
            code = normalize_login_code(value)
            phone, phone_code_hash = data.get("phone"), data.get("phone_code_hash")
            if not phone or not phone_code_hash:
                await state.clear()
                await state.set_state(Flow.login)
                await remove_screen(app, message.chat.id)
                await show_auth_step(app, message.chat.id, state, notice="Начни вход с номера телефона.")
                return
            if code is None:
                await remove_screen(app, message.chat.id)
                await show_auth_step(app, message.chat.id, state, notice="Введи цифры или код с точками.")
                return
            try:
                me = await login_request(
                    app, lambda: app.client.sign_in(phone, code, phone_code_hash=phone_code_hash),
                )
            except errors.SessionPasswordNeededError:
                await state.set_data({"password_dotted": False})
                await state.set_state(Flow.login_password)
                await remove_screen(app, message.chat.id)
                await show_auth_step(app, message.chat.id, state)
                return
        else:
            password = normalize_password(value, bool(data.get("password_dotted", False)))
            if password is None:
                await remove_screen(app, message.chat.id)
                await show_auth_step(app, message.chat.id, state, notice="Проверь пароль и выбранный формат.")
                return
            me = await login_request(app, lambda: app.client.sign_in(password=password))
        await finish_login(app, message.chat.id, state, me)
    except (errors.RPCError, OSError, asyncio.TimeoutError, ValueError, RuntimeError) as exc:
        # Ответ на авторизацию мог потеряться уже после успешного входа.
        if isinstance(exc, (OSError, asyncio.TimeoutError, RuntimeError)):
            try:
                await app.check_login()
            except (errors.RPCError, OSError, asyncio.TimeoutError):
                pass
            if app.me:
                await finish_login(app, message.chat.id, state, app.me)
                return
        await handle_login_error(app, message.chat.id, state, exc)


@dp.message(F.chat.type == ChatType.PRIVATE)
async def accept_input(message: Message, state: FSMContext, app: Runtime) -> None:
    if message.from_user is None or not app.allows(message.from_user.id):
        return
    current = await state.get_state()
    if current is None:
        return
    chat_id = message.chat.id
    if current in {Flow.login.state, Flow.login_code.state, Flow.login_password.state}:
        await accept_login_input(message, state, app)
        return
    if app.me is None:
        await remove_screen(app, chat_id)
        await show_login(app, chat_id, state)
        return
    account_id = app.me.id

    if current == Flow.content.state:
        photo_id = message.photo[-1].file_id if message.photo else None
        text = (message.caption or "") if photo_id else (message.text or "")
        entities = message.caption_entities if photo_id else message.entities
        if message.media_group_id or (not photo_id and not text.strip()):
            await message.answer("Пришли одно фото, фото с подписью или текст.")
            return
        if len(text) > (1024 if photo_id else 4096):
            await message.answer("Текст слишком длинный. Лимит 1024 для подписи и 4096 для текста.")
            return
        content = Content(
            photo_id, text, parse_custom_emoji(text, entities or ()), parse_formatting(entities or ()),
        )
        app.store.save_content(account_id, content)
        await state.clear()
        await remove_screen(app, chat_id)
        await show(
            app, chat_id, f"✅ Контент сохранён.\nПремиум-эмодзи <b>{len(content.emoji)}</b>",
            keyboard(
                [button("👁 Предпросмотр", "preview"), button("🚀 К выбору групп", "start_mailing")],
                back_menu(),
            ),
        )
    elif current in {Flow.delay.state, Flow.report.state}:
        raw = (message.text or "").strip().replace(",", ".")
        if current == Flow.delay.state:
            if not re.fullmatch(r"[0-9]{1,4}(?:\.[0-9]{1,3})?", raw) or not MIN_DELAY <= float(raw) <= MAX_DELAY:
                await message.answer(f"Нужна задержка от {MIN_DELAY:g} до {MAX_DELAY:g} сек.")
                return
            app.store.set_intervals(account_id, delay=float(raw))
        else:
            if not re.fullmatch(r"[0-9]{1,4}", raw) or not 1 <= int(raw) <= MAX_REPORT_MINUTES:
                await message.answer(f"Нужно целое число от 1 до {MAX_REPORT_MINUTES} минут.")
                return
            app.store.set_intervals(account_id, minutes=int(raw))
        await state.clear()
        await remove_screen(app, chat_id)
        await show_settings(app, chat_id, account_id)
    elif current == Flow.manual_group.state:
        remaining = app.store.profile(account_id)["flood_until"] - time.time()
        if remaining > 0:
            await message.answer(f"Пауза Telegram ещё около {int(remaining) + 1} сек.")
            return
        try:
            group = await resolve_group(app, (message.text or "").strip())
        except FLOOD_ERRORS as exc:
            seconds = remember_flood(app, account_id, exc)
            await message.answer(f"Telegram попросил паузу на {seconds} сек.")
            return
        except AUTH_ERRORS:
            app.me = None
            await remove_screen(app, chat_id)
            await show_login(app, chat_id, state)
            return
        except (errors.RPCError, OSError, asyncio.TimeoutError, ValueError) as exc:
            LOG.info("Ручной поиск группы: %s", type(exc).__name__)
            group = None
        if group is None:
            await message.answer(
                "Группа не найдена. Проверь @username или полный ID со знаком минус "
                "и убедись, что аккаунт состоит в группе.",
            )
            return
        app.groups[group.peer_id] = group
        app.store.select_group(account_id, group)
        await state.set_state(Flow.groups)
        await remove_screen(app, chat_id)
        await show_groups(app, chat_id, account_id, state)
    elif current == Flow.group_search.state:
        query = (message.text or "").strip()
        if not 1 <= len(query) <= 80:
            await message.answer("Пришли текст запроса длиной до 80 символов.")
            return
        await state.set_state(Flow.groups)
        await state.update_data(group_query=query)
        await remove_screen(app, chat_id)
        await show_groups(app, chat_id, account_id, state)
    elif current == Flow.set_name.state:
        name = " ".join((message.text or "").split())
        if not 1 <= len(name) <= 48:
            await message.answer("Пришли название набора длиной до 48 символов.")
            return
        if not app.store.save_set(account_id, name):
            await message.answer("Выбери группы перед сохранением набора.")
            return
        await state.set_state(Flow.groups)
        await remove_screen(app, chat_id)
        await show_sets(app, chat_id, account_id, 0)


@dp.errors()
async def report_ui_error(event: ErrorEvent, app: Runtime) -> bool:
    # Токен и произвольный пользовательский ввод не попадают в лог ошибок.
    LOG.error("Ошибка интерфейса: %s", type(event.exception).__name__)
    callback = event.update.callback_query
    msg = event.update.message or (callback.message if callback else None)
    user = callback.from_user if callback else getattr(msg, "from_user", None)
    if isinstance(msg, Message) and msg.chat.type == ChatType.PRIVATE and user and app.allows(user.id):
        if not isinstance(event.exception, TelegramRetryAfter):
            with suppress(TelegramAPIError):
                await app.bot.send_message(msg.chat.id, "Экран не загрузился. Открой /start.")
    return True


# 8. Рассылка. Групповые отправки выполняет только Telethon.
class RunStopped(Exception):
    """Владелец остановил очередь между отправками."""


class RunFailed(Exception):
    """Ошибка подготовки с понятным сообщением для владельца."""


T = TypeVar("T")


async def wait_or_stop(stop: asyncio.Event, seconds: float) -> None:
    if stop.is_set():
        raise RunStopped
    if seconds <= 0:
        return
    try:
        await asyncio.wait_for(stop.wait(), timeout=seconds)
    except asyncio.TimeoutError:
        return
    raise RunStopped


async def mtproto_call(
    app: Runtime, account_id: int, operation: Callable[[], Awaitable[T]], *,
    target_id: int | None = None,
) -> T:
    sending = target_id is not None
    while True:
        profile = app.store.profile(account_id)
        deadline = profile["next_send_at" if sending else "flood_until"]
        await wait_or_stop(app.stop, deadline - time.time())
        # За время ожидания другая операция могла продлить паузу.
        profile = app.store.profile(account_id)
        if profile["next_send_at" if sending else "flood_until"] > time.time():
            continue
        delay = profile["delay"]
        if sending:
            app.store.defer(account_id, time.time() + delay)
        try:
            result = await asyncio.wait_for(operation(), timeout=RPC_TIMEOUT)
        except FLOOD_ERRORS as exc:
            remember_flood(app, account_id, exc, rejected_target=target_id)
            continue
        finally:
            if sending:
                app.store.defer(account_id, time.time() + delay)
        return result


async def prepare_emoji(
    app: Runtime, account_id: int, content: Content, premium: bool, *, preview: bool = False,
) -> list[types.MessageEntityCustomEmoji]:
    ids = [str(emoji.document_id) for emoji in content.emoji]
    try:
        found = await lookup_emoji(app.bot, [*PREMIUM_EMOJI.values(), *ids], retry=not preview)
    except TelegramAPIError as exc:
        LOG.warning("Проверка custom emoji: %s", type(exc).__name__)
        if ids:
            raise RunFailed("Telegram не подтвердил custom emoji. Попробуй запустить рассылку снова.") from exc
        return []
    app.menu_emoji = {key: found[key] for key in PREMIUM_EMOJI.values() if key in found}
    valid = list(dict.fromkeys(int(emoji_id) for emoji_id in ids if emoji_id in found))
    if not valid:
        return []
    request = functions.messages.GetCustomEmojiDocumentsRequest(document_id=valid)
    if preview:
        if app.store.profile(account_id)["flood_until"] > time.time():
            raise RunFailed("Telegram временно приостановил запросы.")
        try:
            documents = await app.client(request)
        except FLOOD_ERRORS as exc:
            remember_flood(app, account_id, exc)
            raise RunFailed("Telegram временно приостановил запросы.") from exc
    else:
        documents = await mtproto_call(app, account_id, lambda: app.client(request))
    attrs = {
        doc.id: attr
        for doc in documents if isinstance(doc, types.Document)
        for attr in doc.attributes if isinstance(attr, types.DocumentAttributeCustomEmoji)
    }
    utf16 = content.text.encode("utf-16-le")
    entities = []
    for emoji in content.emoji:
        attr = attrs.get(emoji.document_id)
        span = utf16[emoji.offset * 2:(emoji.offset + emoji.length) * 2].decode("utf-16-le")
        if attr and (premium or attr.free) and span == attr.alt:
            entities.append(types.MessageEntityCustomEmoji(
                offset=emoji.offset, length=emoji.length, document_id=emoji.document_id,
            ))
        else:
            LOG.warning("Custom emoji %s будет отправлен обычным эмодзи", emoji.document_id)
    return entities


async def resolve_selected(app: Runtime, account_id: int, saved: Group) -> Group | None:
    known = app.groups.get(saved.peer_id)
    if known:
        return known

    async def fetch() -> Group | None:
        try:
            entity = await app.client.get_entity(saved.peer_id)
        except ValueError:
            if not saved.username:
                raise
            entity = await app.client.get_entity(f"@{saved.username}")
        group = as_group(entity)
        return group if group and group.peer_id == saved.peer_id else None

    return await mtproto_call(app, account_id, fetch)


def start_task(app: Runtime, run_id: int, account_id: int) -> None:
    app.stop = asyncio.Event()
    app.run_id = run_id
    app.current_group = None
    app.last_report = time.monotonic()
    app.task = asyncio.create_task(
        mailer(app, run_id, account_id, bool(app.me and app.me.premium)),
        name=f"mailing-{run_id}",
    )


async def launch(
    app: Runtime, chat_id: int, account_id: int, *, test_group: Group | None = None,
) -> None:
    if app.active:
        await show_status(app, chat_id, account_id)
        return
    content = app.store.load_content(account_id)
    groups = (test_group,) if test_group else tuple(app.store.groups(account_id).values())
    if content is None or not groups or app.me is None:
        await show(app, chat_id, "Для запуска подключи аккаунт, сохрани контент и выбери группы.",
                   keyboard(back_menu()))
        return
    run_id = app.store.new_run(account_id, chat_id, groups, content, kind="test" if test_group else "bulk")
    if run_id is not None:
        start_task(app, run_id, account_id)
    await show_status(app, chat_id, account_id, run_id)


def target_group(row: sqlite3.Row) -> Group:
    return Group(row["peer_id"], row["title"], row["username"])


async def launch_retry(app: Runtime, chat_id: int, account_id: int, run: sqlite3.Row) -> None:
    if app.active:
        await show_status(app, chat_id, account_id)
        return
    source = run["id"]
    content = app.store.snapshot(source)
    targets = app.store.retryable(source) if run["state"] != "running" else []
    if content is None or not targets:
        await show_results(app, chat_id, account_id, source, 0)
        return
    run_id = app.store.new_run(
        account_id, chat_id, [target_group(row) for row in targets], content,
        kind="retry", source=source, retries={row["peer_id"]: row["id"] for row in targets},
    )
    if run_id is not None:
        start_task(app, run_id, account_id)
    await show_status(app, chat_id, account_id, run_id)


async def resume_run(app: Runtime, chat_id: int, account_id: int, run_id: int) -> None:
    if app.active:
        await show_status(app, chat_id, account_id)
        return
    if app.me and app.me.id == account_id and app.store.reopen(run_id, account_id, chat_id):
        start_task(app, run_id, account_id)
    await show_status(app, chat_id, account_id, run_id)


def delivery_error(exc: Exception, sending: bool) -> tuple[str, str]:
    name = type(exc).__name__
    if name in {
        "ChatWriteForbiddenError", "ChatSendMediaForbiddenError", "ChatSendPhotosForbiddenError",
        "ChatSendPlainForbiddenError", "ChatAdminRequiredError",
    }:
        return "failed", "Нет прав на публикацию этого поста."
    if isinstance(exc, errors.UserBannedInChannelError):
        return "failed", "Аккаунт заблокирован в группе."
    if name in {"ChannelPrivateError", "PeerIdInvalidError"}:
        return "failed", "Группа недоступна."
    rejected = isinstance(exc, errors.RPCError) and exc.code in {400, 401, 403, 404, 406}
    if sending and (not rejected or isinstance(exc, errors.RandomIdDuplicateError)):
        return "uncertain", "Telegram не подтвердил отправку. Проверь публикацию в группе."
    return "failed", f"Запрос не выполнен ({name})."


async def mailer(
    app: Runtime, run_id: int, account_id: int, premium: bool,
) -> None:
    state = "failed"
    notes = []
    try:
        await wait_or_stop(app.stop, 0)
        content = app.store.snapshot(run_id)
        if content is None:
            raise RunFailed("Снимок поста недоступен.")
        if not app.groups:
            await mtproto_call(app, account_id, lambda: refresh_groups(app))
        custom = await prepare_emoji(app, account_id, content, premium)
        entities = sorted([*mtproto_formatting(content), *custom], key=lambda item: (item.offset, -item.length))
        dropped = len(content.emoji) - len(custom)
        if dropped:
            notes.append(f"Заменено обычными эмодзи {dropped}.")
        photo_data = None
        if content.photo_file_id:
            photo = io.BytesIO()
            try:
                await app.bot.download(content.photo_file_id, destination=photo)
            except TelegramAPIError as exc:
                raise RunFailed("Не удалось скачать фото. Сохрани его повторно.") from exc
            photo_data = photo.getvalue()
            if not photo_data:
                raise RunFailed("Фото недоступно. Сохрани его повторно.")

        uploaded = None
        uploaded_at = 0.0

        async def send(peer: types.TypeInputPeer, target_id: int) -> object:
            nonlocal uploaded, uploaded_at
            # Один загруженный файл на очередь. Долгая пауза обновит ссылку.
            if photo_data is not None and (uploaded is None or time.monotonic() - uploaded_at >= 3600):
                uploaded = await app.client.upload_file(photo_data, file_name="acczHELP-photo.jpg")
                uploaded_at = time.monotonic()
            await wait_or_stop(app.stop, 0)
            # Состояние фиксируется после загрузки фото, прямо перед публикацией.
            app.store.begin_target(target_id)
            if photo_data is None:
                return await app.client.send_message(
                    peer, content.text, parse_mode=None,
                    formatting_entities=entities, link_preview=False,
                )
            return await app.client.send_file(
                peer, types.InputMediaUploadedPhoto(file=uploaded),
                caption=content.text, parse_mode=None, formatting_entities=entities,
            )

        for target in app.store.pending(run_id):
            await wait_or_stop(app.stop, 0)
            target_id = target["id"]
            saved = target_group(target)
            app.current_group = saved.title
            try:
                group = await resolve_selected(app, account_id, saved)
                if group is None or group.peer is None:
                    LOG.info("Группа %s недоступна для текущего аккаунта", saved.peer_id)
                    app.store.record(run_id, target_id, "failed", "Группа недоступна для текущего аккаунта.")
                    continue
                peer = group.peer
                sent = await mtproto_call(app, account_id, lambda: send(peer, target_id), target_id=target_id)
            except AUTH_ERRORS:
                if app.store.target_sending(target_id):
                    app.store.record(run_id, target_id, "failed", "Telegram отклонил текущую сессию.")
                raise
            except errors.PeerFloodError:
                app.store.record(run_id, target_id, "failed", "Telegram ограничил исходящие сообщения.")
                raise
            except (errors.RPCError, ValueError, OSError, asyncio.TimeoutError) as exc:
                outcome, detail = delivery_error(exc, app.store.target_sending(target_id))
                LOG.warning("Отправка в группу %s: %s", saved.peer_id, type(exc).__name__)
                app.store.record(run_id, target_id, outcome, detail)
            else:
                app.store.record(run_id, target_id, "sent", message_id=getattr(sent, "id", None))
        state = "done"
    except RunStopped:
        state = "stopped"
    except asyncio.CancelledError:
        state = "stopped" if app.stop.is_set() else "interrupted"
        notes.append("Процесс остановлен. Состояние очереди сохранено.")
        raise
    except AUTH_ERRORS as exc:
        app.me = None
        notes.append("Пользовательская сессия отключена. Выполни вход повторно.")
        LOG.warning("Сессия MTProto: %s", type(exc).__name__)
    except errors.PeerFloodError:
        notes.append("Telegram ограничил исходящие сообщения аккаунта. Очередь остановлена.")
    except RunFailed as exc:
        notes.append(str(exc))
    except Exception as exc:
        LOG.error("Рассылка %s остановлена: %s", run_id, type(exc).__name__)
        notes.append(f"Рассылка прервана на этапе подготовки или отправки ({type(exc).__name__}).")
    finally:
        app.current_group = None
        app.store.finish(run_id, state, " ".join(notes))

    if not await refresh_live_status(app, force=True):
        run = app.store.run(run_id, account_id)
        if run:
            await send_report(app, account_id, run)


# 9. Периодические отчёты только во время активной рассылки
async def refresh_live_status(app: Runtime, *, force: bool = False) -> bool:
    async with app.live_lock:
        screen, run_id = app.screen, app.live_run_id
        if not screen or run_id is None or run_id != app.run_id:
            return False
        now = time.monotonic()
        if now < app.last_live_edit or (not force and now - app.last_live_edit < LIVE_REFRESH):
            return True
        run = app.store.run(run_id)
        if run is None:
            return False
        text = status_text(app, run["account_id"], run)
        if text == app.live_text:
            return True
        app.last_live_edit = now
        try:
            await app.bot.edit_message_text(
                text, chat_id=screen.chat.id, message_id=screen.message_id,
                reply_markup=status_keyboard(app, run),
            )
        except TelegramRetryAfter as exc:
            if app.screen is screen:
                app.last_live_edit = now + exc.retry_after + 1
            return True
        except TelegramBadRequest as exc:
            if "message is not modified" not in exc.message.lower():
                if app.screen is screen:
                    app.live_run_id = None
                return False
        except TelegramAPIError as exc:
            LOG.debug("Не обновлён статус %s: %s", run_id, type(exc).__name__)
            return False
        if app.screen is screen:
            app.live_text = text
            if run["state"] != "running":
                app.live_run_id = None
        return True


async def send_report(app: Runtime, account_id: int, run: sqlite3.Row) -> None:
    try:
        await app.bot.send_message(run["chat_id"], status_text(app, account_id, run))
    except TelegramAPIError as exc:
        LOG.warning("Не отправлен отчёт %s: %s", run["id"], type(exc).__name__)


async def periodic_status(app: Runtime) -> None:
    while True:
        await asyncio.sleep(2)
        await refresh_live_status(app)
        if app.run_id is None:
            continue
        run = app.store.run(app.run_id)
        if not run or run["state"] != "running":
            continue
        now = time.monotonic()
        interval = app.store.profile(run["account_id"])["report_minutes"] * 60
        if now - app.last_report >= interval:
            app.last_report = now
            await send_report(app, run["account_id"], run)


# 10. Локальная авторизация, health-check и запуск
def https_origin(value: str) -> str:
    value = value.strip().rstrip("/")
    url = urlsplit(value)
    if (
        url.scheme != "https" or not url.hostname or url.username is not None
        or url.path or url.query or url.fragment or any(char.isspace() for char in value)
    ):
        raise ValueError("Нужен HTTPS-адрес сервиса без пути.")
    if url.port is not None and not 1 <= url.port <= 65535:
        raise ValueError("Проверь порт HTTPS-адреса.")
    return value


def validate_config(*, polling: bool) -> None:
    if not API_ID.isdecimal() or not 1 <= int(API_ID) < 2**31:
        raise SystemExit("Укажи положительный числовой API_ID.")
    if not re.fullmatch(r"[A-Fa-f0-9]{32}", API_HASH):
        raise SystemExit("Укажи API_HASH из my.telegram.org.")
    if polling and not BOT_TOKEN:
        raise SystemExit("Укажи BOT_TOKEN из BotFather.")
    if OWNER_ID and not re.fullmatch(r"[0-9]{1,19}", OWNER_ID):
        raise SystemExit("OWNER_ID должен быть числовым Telegram ID или 0.")
    if PORT and (not PORT.isdecimal() or not 1 <= int(PORT) <= 65535):
        raise SystemExit("PORT должен быть целым числом от 1 до 65535.")
    if polling and PUBLIC_BASE_URL:
        try:
            https_origin(PUBLIC_BASE_URL)
        except ValueError:
            raise SystemExit("Укажи в PUBLIC_BASE_URL HTTPS-адрес сервиса без пути.") from None


def normalize_login_code(value: str) -> str | None:
    value = re.sub(r"[\s-]", "", value)
    if re.fullmatch(r"[0-9]{4,8}|[0-9](?:\.[0-9]){3,7}", value):
        return value.replace(".", "")
    return None


def normalize_password(value: str, dotted: bool) -> str | None:
    if not value:
        return None
    if not dotted:
        return value
    if len(value) % 2 == 1 and all(mark == "." for mark in value[1::2]):
        return value[::2]
    return None


async def terminal_login(client: TelegramClient, *, dotted_password: bool = False) -> types.User:
    if not sys.stdin.isatty():
        raise SystemExit("Для --login нужен интерактивный терминал.")
    phone = re.sub(r"[\s()-]", "", input("Телефон с кодом страны (+…): "))
    if not re.fullmatch(r"\+[1-9][0-9]{6,14}", phone):
        raise SystemExit("Укажи телефон в международном формате, начиная с +.")
    sent_code = await client.send_code_request(phone)
    for _ in range(3):
        code = normalize_login_code(getpass.getpass("Код от Telegram (например, 2.3.4.5.6): "))
        if code is None:
            print("Введи цифры или код с точками между ними.", file=sys.stderr)
            continue
        try:
            return await client.sign_in(phone, code, phone_code_hash=sent_code.phone_code_hash)
        except (errors.PhoneCodeInvalidError, errors.PhoneCodeEmptyError):
            print("Код неверный. Попробуй ещё раз.", file=sys.stderr)
        except errors.SessionPasswordNeededError:
            for _ in range(3):
                password = normalize_password(getpass.getpass("Пароль 2FA: "), dotted_password)
                if password is None:
                    print("Проверь пароль и формат точек.", file=sys.stderr)
                    continue
                try:
                    return await client.sign_in(password=password)
                except errors.PasswordHashInvalidError:
                    print("Пароль 2FA неверный.", file=sys.stderr)
            raise SystemExit("Вход остановлен после трёх неверных паролей.")
    raise SystemExit("Вход остановлен после трёх неверных кодов.")


async def render_pairing_request(remote: str, key: str, *, session: str | None = None) -> None:
    if not re.fullmatch(r"[A-Za-z0-9_-]{32}", key):
        raise SystemExit("Скопируй ключ подключения из меню acczHELP.")
    try:
        async with ClientSession(timeout=ClientTimeout(total=65), trust_env=False) as http:
            async with http.post(
                f"{remote}/connect/session", json={} if session is None else {"session": session},
                headers={"Authorization": f"Bearer {key}"}, allow_redirects=False,
            ) as response:
                status = response.status
                result = await response.json() if response.content_type == "application/json" else {}
    except (ClientError, OSError, ValueError, asyncio.TimeoutError):
        raise SystemExit("Render не ответил. Проверь адрес сервиса и статус входа в боте.") from None
    expected = "key_ok" if session is None else "linked"
    if status == 200 and isinstance(result, dict) and result.get("result") == expected:
        return
    reason = result.get("result") if isinstance(result, dict) else None
    messages = {
        "invalid_key": "Ключ подключения недействителен. Возьми свежий ключ из меню acczHELP.",
        "wrong_account": "Войди в Telegram-аккаунт, указанный в OWNER_ID.",
        "already_linked": "Аккаунт уже подключён. Проверь вход в меню acczHELP.",
        "busy": "На Render активна очередь. Дождись завершения и повтори подключение.",
        "invalid_session": "Telegram не подтвердил авторизацию. Повтори вход.",
    }
    message = messages.get(reason) if isinstance(reason, str) else None
    raise SystemExit(message or f"Render пока не принял подключение (HTTP {status}).")


async def local_session_command(
    *, export: bool, remote: str = "", dotted_password: bool = False,
) -> None:
    if export and not SESSION_PATH.is_file():
        raise SystemExit("Сначала выполни python bot.py --login.")
    key = ""
    exported = ""
    if remote:
        if not sys.stdin.isatty():
            raise SystemExit("Для подключения к Render нужен интерактивный терминал.")
        key = getpass.getpass("Одноразовый ключ подключения из acczHELP: ").strip()
        await render_pairing_request(remote, key)
    client = make_client(local_session=True, session=MemorySession() if remote else None)
    try:
        await client.connect()
        me = await client.get_me()
        if me is None:
            if export:
                raise SystemExit("Сначала выполни python bot.py --login.")
            me = await terminal_login(client, dotted_password=dotted_password)
        if not isinstance(me, types.User) or me.bot:
            raise SystemExit("Нужен пользовательский аккаунт Telegram.")
        if remote:
            exported = StringSession.save(client.session)
        elif export:
            print(StringSession.save(client.session))
        else:
            print(f"Аккаунт подключён. Telegram ID {me.id}. Сессия сохранена в {SESSION_PATH}.")
    except FLOOD_ERRORS as exc:
        raise SystemExit(f"Telegram попросил подождать {exc.seconds} сек перед входом.") from None
    except errors.PhoneCodeExpiredError:
        raise SystemExit("Код истёк. Запусти --login повторно.") from None
    except (errors.RPCError, OSError, asyncio.TimeoutError) as exc:
        raise SystemExit(f"Вход недоступен ({type(exc).__name__}).") from None
    finally:
        await client.disconnect()

    if remote:
        # Отдаём готовую сессию только после отключения локального MTProto-клиента.
        await render_pairing_request(remote, key, session=exported)
        print("Аккаунт подключён к Render. Устройство acczHELP. Нажми «Проверить вход» в боте.")


def pairing_reply(result: str, status: int = 200) -> web.Response:
    return web.json_response({"result": result}, status=status, headers={"Cache-Control": "no-store"})


async def accept_render_session(app: Runtime, request: web.Request) -> web.Response:
    match = re.fullmatch(r"Bearer ([A-Za-z0-9_-]{32})", request.headers.get("Authorization", ""))
    if not match or request.content_type != "application/json":
        return pairing_reply("invalid_key", 403)
    async with app.login_lock:
        pairing = app.pairing
        if (
            pairing is None or pairing.expires_at <= time.monotonic() or pairing.owner_id != app.owner_id
            or not hmac.compare_digest(pairing.token, match[1])
        ):
            return pairing_reply("invalid_key", 403)
        if app.me:
            return pairing_reply("already_linked", 409)
        if app.active:
            return pairing_reply("busy", 409)
        try:
            data = await request.json()
            if data == {}:
                return pairing_reply("key_ok")
            raw = data.get("session") if isinstance(data, dict) else None
            if not isinstance(raw, str) or not 1 <= len(raw) <= 512:
                return pairing_reply("invalid_session", 400)
            source = StringSession(raw)
            if not source.auth_key:
                return pairing_reply("invalid_session", 400)
        except (ValueError, struct.error):
            return pairing_reply("invalid_session", 400)

        try:
            config = await asyncio.wait_for(app.client(functions.help.GetConfigRequest()), timeout=10)
            # Адрес берём из ответа Telegram, чтобы импорт не открывал произвольные соединения.
            options = [
                dc for dc in config.dc_options if dc.id == source.dc_id and dc.port == 443
                and not (dc.ipv6 or dc.media_only or dc.cdn or dc.tcpo_only or dc.secret)
            ]
            if not options:
                return pairing_reply("invalid_session", 400)
            dc = next((item for item in options if item.ip_address == source.server_address), options[0])
            source.set_dc(dc.id, dc.ip_address, dc.port)
            candidate = make_client(session=source)
            try:
                await asyncio.wait_for(candidate.connect(), timeout=15)
                me = await asyncio.wait_for(candidate.get_me(), timeout=10)
            finally:
                await candidate.disconnect()
            if not isinstance(me, types.User) or me.bot:
                return pairing_reply("invalid_session", 400)
            if me.id != (app.account_id or app.owner_id):
                return pairing_reply("wrong_account", 403)

            await app.client.disconnect()
            app.client = make_client(session=install_session(source))
            app.pairing = None
            try:
                await asyncio.wait_for(app.client.connect(), timeout=15)
            except (errors.RPCError, OSError, asyncio.TimeoutError) as exc:
                LOG.warning("Повторное подключение MTProto: %s", type(exc).__name__)
            else:
                app.set_login(me)
            return pairing_reply("linked")
        except (errors.RPCError, OSError, sqlite3.Error, asyncio.TimeoutError) as exc:
            LOG.warning("Подключение сессии к Render: %s", type(exc).__name__)
            return pairing_reply("unavailable", 503)


async def health_check(_: web.Request) -> web.Response:
    return web.json_response({"status": "ok", "service": BOT_NAME})


async def sender_ready(app: Runtime) -> bool:
    if app.login_lock.locked():
        return app.me is not None and app.client.is_connected()
    if app.me and app.store.profile(app.me.id)["flood_until"] > time.time():
        return app.client.is_connected()
    try:
        await app.check_login()
    except FLOOD_ERRORS as exc:
        if app.me:
            remember_flood(app, app.me.id, exc)
        return app.me is not None
    return app.me is not None


async def check_readiness(app: Runtime) -> None:
    try:
        app.store.db.execute("SELECT account_id FROM profiles LIMIT 1").fetchone()
    except sqlite3.Error:
        database_ok = False
    else:
        database_ok = True
    bot_result, sender_result = await asyncio.gather(
        asyncio.wait_for(app.bot.get_me(), timeout=8),
        asyncio.wait_for(sender_ready(app), timeout=8),
        return_exceptions=True,
    )
    ready = database_ok and not isinstance(bot_result, BaseException) and sender_result is True
    if ready != app.ready or not app.readiness_checked_at:
        LOG.info("Готовность Telegram: %s", "готов" if ready else "проверка не пройдена")
    app.ready = ready
    app.readiness_checked_at = time.monotonic()


async def readiness_loop(app: Runtime) -> None:
    while True:
        await check_readiness(app)
        await asyncio.sleep(READY_INTERVAL)


async def serve_health(app: Runtime) -> web.AppRunner:
    async def ready_check(_: web.Request) -> web.Response:
        fresh = time.monotonic() - app.readiness_checked_at < READY_INTERVAL * 2
        ready = app.ready and app.me is not None and fresh
        return web.json_response(
            {"status": "ready" if ready else "unavailable"},
            status=200 if ready else 503, headers={"Cache-Control": "no-store"},
        )

    async def connect_render(request: web.Request) -> web.Response:
        return await accept_render_session(app, request)

    service = web.Application(client_max_size=4096)
    service.router.add_get("/healthz", health_check)
    service.router.add_get("/readyz", ready_check)
    if PUBLIC_BASE_URL:
        service.router.add_post("/connect/session", connect_render)
    runner = web.AppRunner(service, access_log=None)
    await runner.setup()
    try:
        await web.TCPSite(runner, "0.0.0.0", int(PORT)).start()
    except BaseException:
        await runner.cleanup()
        raise
    return runner


@contextmanager
def lock_data_dir():
    # Отдельная блокировка удерживается до выхода и освобождается при падении процесса.
    guard = sqlite3.connect(DATA_DIR / ".acczhelp.lock", timeout=0)
    try:
        try:
            guard.execute("BEGIN EXCLUSIVE")
        except sqlite3.OperationalError as exc:
            if "locked" in str(exc).lower():
                raise SystemExit("Останови другой экземпляр acczHELP, использующий эту папку данных.") from None
            raise
        yield
    finally:
        guard.close()


async def run_service() -> None:
    bot = make_bot()
    client = make_client()
    db = init_db()
    app = Runtime(bot, client, Store(db))
    reporter = None
    readiness = None
    health = None
    try:
        app.store.recover_runs()
        await client.connect()
        await app.check_login()
        bot_user = await bot.get_me()
        if bot_user.first_name != BOT_NAME:
            try:
                await bot.set_my_name(name=BOT_NAME)
            except TelegramAPIError as exc:
                LOG.warning("Не удалось задать имя бота: %s", type(exc).__name__)
        await bot.delete_webhook(drop_pending_updates=False)
        try:
            app.menu_emoji = await lookup_emoji(bot, list(PREMIUM_EMOJI.values()))
        except TelegramAPIError as exc:
            LOG.warning("Проверка эмодзи меню: %s", type(exc).__name__)

        if PORT:
            health = await serve_health(app)
            readiness = asyncio.create_task(readiness_loop(app), name="readiness")
            LOG.info("HTTP /healthz и /readyz открыты на порту %s", PORT)
        reporter = asyncio.create_task(periodic_status(app), name="periodic-status")
        if app.me and (pending := app.store.interrupted_run(app.me.id)):
            LOG.info("Возобновляю запуск %s после перезапуска", pending["id"])
            with suppress(TelegramAPIError):
                await resume_run(app, app.owner_id, app.me.id, pending["id"])
        LOG.info("acczHELP запущен. MTProto %s", "авторизован" if app.me else "ожидает входа")
        await dp.start_polling(
            bot, app=app, allowed_updates=dp.resolve_used_update_types(),
            handle_as_tasks=False, close_bot_session=False,
        )
    finally:
        tasks = [task for task in (reporter, readiness, app.task) if task is not None]
        for task in tasks:
            task.cancel()
        for outcome in await asyncio.gather(*tasks, return_exceptions=True):
            if isinstance(outcome, Exception):
                LOG.error("Фоновая задача: %s", type(outcome).__name__)
        if health:
            await health.cleanup()
        try:
            await app.client.disconnect()
        finally:
            await bot.session.close()
            db.close()


async def main() -> None:
    parser = argparse.ArgumentParser(description=f"{BOT_NAME} — Telegram-панель рассылки")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--login", action="store_true", help="создать локальную пользовательскую сессию")
    modes.add_argument("--export-session", action="store_true", help="вывести секрет сессии для Render")
    parser.add_argument("--render", default="", help="HTTPS-адрес своего Render для передачи готовой авторизации")
    parser.add_argument("--dotted-password", action="store_true", help="пароль 2FA с точкой между символами")
    args = parser.parse_args()

    if (args.render or args.dotted_password) and not args.login:
        parser.error("--render и --dotted-password используются вместе с --login")
    try:
        remote = https_origin(args.render) if args.render else ""
    except ValueError as exc:
        parser.error(str(exc))
    local = args.login or args.export_session
    validate_config(polling=not local)
    if os.name != "nt":
        os.umask(0o077)
    if remote:
        await local_session_command(export=False, remote=remote, dotted_password=args.dotted_password)
        return
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    with lock_data_dir():
        if local:
            await local_session_command(export=args.export_session, dotted_password=args.dotted_password)
        else:
            await run_service()


# Встроенный баннер acczHELP в JPEG. Хостинг изображения не нужен.
BANNER_JPEG_B64 = (
    "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"
    "tdMsLm9rvpTt6UqkvkkbqkorMtkcVS6XJHA0rdvuNyjZt45H2nbHo/buvqca+szsdv2zWW7upxVceVOP9LR9K292SdnOgKM793m4"
    "7qPX10vVUM/kR6/Fs86txqxo7RlrfSO/ny8zKaq4zNqPx+3PyPMeh7e1LVruNrpen3V9cPpTt6TqS+S6H1vano+7svowr65VstBt"
    "3zf0ifrKuPKEeSfvaPvFtqdPT7VWmjWNppdquSpWtJU1+YxTu6lV5qVJSfmzxrj9QXdTajFQXv3f2+phrt1zzLyX3+h1vbnY92c6"
    "FwzvYXW4bmPPNzLgo5/IjjPxbO90L6nZWys9Ls7XTraPJUrakoRXwRwvrvMHXfieHXda5ea03L4vbw5ItXs1tTSivdt58/M5SVzK"
    "cuKcnJ+LYKsvE4xVyvXGXYijNs5P1+e8aq+Zx9OTbWOZydrZv1DurqpGhbx5yqTeF/8AsynGMOZ10oym8IzW8Z1pYim8ka7rWk7a"
    "oes1GsqlfHsW1N5k/f4HTd19pFvY8dht+PtfVlcS+s/d4Hza7v697XlXuKsqtSTy23k9Oz4HVr4nW9WPTvf2KqXsKXq095de5ff6"
    "fE7Puze2p7gqeqnP6PZJ+xb03iPx8WZ9n6DHUEtQv+KFhF+yk8SryX2Y+C8ZfBc+nHbY0CF3Sjqep8ULFP73TTxK5a7l4QXfL4Ly"
    "7fK8nUcUoxjGMVGEIrEYRXRJdyPTuJQoQ7C2WMc8d389X+/LaytJ159rW3/PocnXnx8MYRjCEUowhBYjBLokvA27C3cmm0cbZNzm"
    "kztek0IcCnPlCK4pPwS5s+euJ9nHB9bb0EllnCdomt0Nr7TudQmk3Y27ueF/bqv2aUPjJr5s8P31etXq1K1ebqVaknOpN9ZSby38"
    "W2z736UG6PWOx0NS9q5m9QuYZ6RWYUYv/wAcvgj4FXuIZeKcT7j9NWSt7PtJ+1P6L+c/LAqz1VNPQ0KqyYJQZuu4ef73T/ilQrRf"
    "1qFJ/A93RF9510qafeca6b8BOmzmYq3n1t0vyZFfQaFR+z6yHvWRq3b5HfC3b5HBOm/AXq/I596PWxmmlUXl1+Rq1LOcG1KDTXVN"
    "CdCS5nR6LJc0cRKmY5UzlJ27XcYKlHyM5USZW7OOlDHcYpLBvVKZr1I8zlnTwcs6WDVaJaM0osho55QOZwOHFgYYPMwAsEsrmDJa"
    "ESJlMlkNCJYDYmZskTAMiZLEwYgDJDEJgAAACGJ+QhB0AAEIGIYmAgDuABMAYgYEgIBZGBIYAAEACATYhAAAAAAAIQg5eK+Yz3J+"
    "592dpX7KNcqV7ahVktemszpxk0vUUe9o5by49Hp68ZGjw0seMfmHxT+J+uv3N01/8n2v+gj+w8Len7b0bftg02FCjSpReiUniEFF"
    "Z9bV58jktOJ+kVNGnHzBrB5zAAPVEDx3tIXL8KPzPsnoaUqdX0gtAp1acKkHSu8xnFSX94l3M/RKGl6bwrOn2mf+4h+w8q84l6PP"
    "RpyNLJ+RXXvXzEfoF6cdjaUewW9qULS3pyjqFpiUKUYv6/ikeGuzmPH2hbcjJJp6taJprKf36B02t529Jz08hNYOCyvwo/MFj8KP"
    "zP11hpmm5lmwtOr/AMRD9hX3L03u0+1/0Ef2Hmf61/w8/wCB6T8icL8KPzDkvtR+Z+u33M05f+gWn+gj+wX3M01/8n2n+gj+wP8A"
    "W/8Ah5/wGk/Inl4x+YYXjH5n67vTdOX/AKBa/wChj+w+bek1p9lDsE3lOlZW0Jx02TUo0Ypr2o9+C6fGFOajo5+/+AcT80egZX4U"
    "fmb+jw4tdsotLndUlh/lo/WOlpOmrm9Ps8r/ANnh+w672+dq4+rnIksn5HdOrj8xH6x7t07T1tvUmrG1z9Dr8/UR/wCjl5H5Ovov"
    "yV+guxvvSs+rjANYDyEMDvJEPkurS97F7j3R6AVna1+yXUqlxa0Kr+7dVKU6UZPHqqXe0ct5c+jU9eMglk8MZX4UfmPHmvmfrr9z"
    "NM7rC0/0Ef2E/cyw7rG1/wBBH9h5a45/w8/4K0H5FNJdWvmCw3yaz5M/XeOmaf32Nq//AIMf2HC7h2FsnX6M6Ws7U0W+jJYbq2NN"
    "y+EsZXwY48cWd4eYaD8pMYEe3O1/0R9A1K2raj2e3M9GvopyVhcVJVLWq/wYyeZU3/GXkjxruLQ9V27rV3o2t2Nax1C0qOnXoVY4"
    "lCX9Ka5prk000eta3dK6XqPfoQ00cchpAkUkdmCciGugYHgpIlsENBgaRaQsghjRSRSROSUiooaRaRookuRKRSRcYlqJpGJDmTFF"
    "KJaiXGBtGJlKZCiXGBlhDJljSNowMZVTBGBmjAzwotmenbtm8aWTmnXSNaFNmeFHyNylay5cjk9J0a81C7haWNpXuribxGlRpuc3"
    "8EmzojRwss5J3SRw8Ld/gmzRtHJ9D7LtbsC3lqNONzq0LXb9q+bnf1MVMeVOOX88H0bb/ZP2bbf4amq173ctzH7LfqLfP5Meb+LO"
    "KpxWzpbRet9I7+fLzOWrWcd5tR+P25+R5q0jQ7/UrqNpp1lcXlxLlGlQpSqTfwSyfV9q9gG8L+nG51r6Ht61fNyvaidRrypxy/m0"
    "fcLbX6Ol230PbumWOjWvTgtaMYt+945nHXOoXFzNzr1p1JPvlLJw1eLXdTalFQXv3f2XmebU4hRjyzJ+C+78jiNB7J+zbQFGeoTv"
    "dx3UeqqS9TQz+THm/i2d2tNbp6bZqy0PT7LSrVclTtaKgvjjqda9au95H67l1PLq0p13mvJy+PLw5eRzviFZ+w9Pw28+fmcvWvq1"
    "eblWqylJ+LyQqyx1OK9f5gq/mCoY5GCbbyct69LvH69eJxSr57ylW8xdibROT9d5jVU4+FVvvNu3hKo0km8kSglzOiCNqE+hu2dt"
    "WuKkYU4OUm+SXUy2OmRpW7vL+rG2tY9ak+/yS72dW3f2iULKnPT9vwdNc4zrN+3L4rovJGFOnUuZ6KCz7+5HfGnGnHVVeF073+dT"
    "tes6vo21bdzv6sLm8x7NvCXJP8Z/0I+U7u3xq2v1XGpVdK3XKFKHJJe461fX9e8rOrcVXOb8WarbfM+nsOC0rb15+tPr0+BjVuZ1"
    "VojtHp9+psKWXk7TtbRKcqNPVdXhL6E+dChnErl+PlT8+/ovEwbW0KjChT1fW6ebeS4ra0fJ3H40vCn/ADvd15+5uqt7cOvWlmT5"
    "JJYSXcku5Iq8uct06fzf7L933fHl6XD+Ha8Tmtjdq3dS6retqYXJKMYrEYxXRJdyXgbNrltHH28Ms5Szg8o8SriKwj663t8HN6TT"
    "4ppnP6rXja6NGlxqm7mXDKTeFGnHnOT8jidFhKdWEIrMpNJHS/SR3LHRtl39OhV4a95jSrXD54abrTX8HiX8JHkwoO6uoUl3v8+/"
    "yPSeKcHJ9255q7Rdxy3PvDUtay/U16uLeL+zRiuGmv4qT97Z1apUYV6vPC5I1J1OfU/S/VpxUI8lsjyKeW8szOqONZo03MOMntcH"
    "fTng5KncNd5uUL2UWvaODjU8zLCrzXM3hXaPRo1mjt9hqsk0pKMl5o7DZ1dO1GKpXtunnkpJ4kvifOreu01zOf0q9cXHmdcZKqt+"
    "Z71ndZ2kdk1nZdalaTv7CX0q0jzm0vap/lLw8zp93YuDeYn1fYut1KFzTlGfk0+aa7013ryOW7Uth2v3Ipbr0GjiwuHw3NCPP6LV"
    "8F+I+7w6HD6aqVZUK/fyfv6P39Ov19Kpb05Yxtnl8en2PP1zRw3yNGtA7FqNq4TawcPc08G9elg8O5t9LOMqRMMkbdWJglE8+UcH"
    "lThhnBA0A8HjYOQQnyKaJx5ktASyWU+gjNolksRXeLHMyaJELD7kfYuxn0fN69o1tQ1bhpaLoNXnC/uk26yzhulTXOXveI+bPUWy"
    "fRa7LtBpU56pY3W4rpL2ql/Wap58qcMRx78nlXPFLeg9LeX0RLkj8+uXe0viGMrK5+4/Uuz7NOzuyoxo22xtt04JYSWmUn+dxOL1"
    "/sW7LNcpyhfbE0NOSxx29srea/hU+FnCuPU87wYtR+Y3uA9f9r/oi0KVjW1Ps3v68q0E5PS76opes8qVXlh+Cn1/CR5Gv7W5sL6t"
    "ZXtvVt7mhUlTrUqsHGdOaeHGSfNNPuPTtrulcxzBhkwiGcltjQtW3LrdtouhafcahqF1Pho0KMcyk+9+CS6tvkl1OhtJZbA4wbjj"
    "ry957M7LfRA0qjbUb7tC1Wte3MkpS0+wqerow/FlVxxTf5PCvNn3Xb/ZH2Z6DRVLTti6DDHLjq2ca0375VOJv5nkVuNUIPEVqFk/"
    "L3l0TT9zBryP1O1Tsy7O9UoOjfbI25Wg1jnptJNe5pJo+Sdo3on9n+t21WrteVztq/w3BUpyrW0n4SpzeUvyZL3MilxujJ4kmhHg"
    "sR27tQ7O909nO4ZaNuaw9TOScre4pvioXMF9qnLvXinhrvSOpYPXhKNSOqLygEGDmtl7U3BvLcFDQttabWv7+vzUIclCK6znJ8ox"
    "Xe3yPYPZZ6Ie29PtqN5v7Ua2s3rSc7O0qOjawfg5L25+/MV5HLc3tK22m9+gjxG1jry9/IEs9OfuP1I0fsl7MtHoqlYbE29Tiu+d"
    "jCpJ++U02/mGtdk3ZprNF0b/AGJt6pF98LGFOS90oJNfBnm/65Tz7LDB+W4Ht7tP9ELa+oWtW72JqFxot8k3C0uqjrWs34cT9uHv"
    "zJeR473vtbXdl7iuNA3Hp9Wwv7d+1CfNSi+k4yXKUX3SXI9G2vaVwvVe/QRwjFh+DO79hOhaZubtd2zoOtW30rT72+jSuKXG48ce"
    "GTxmLTXRdD3NT9GjsYklnaH/AP31/wCuY3XEKdtJRkmHM/OLD8GPD8Gfo/8A2s3Yuv8Amev/AK+v/XD+1p7F8f8AA+P/ANdX/rnN"
    "/rVDo/L7hhn5wcL8GGH4H6PP0Z+xj/1PX/11f+uKXo09i6g3/sPWV/7fcf1w/wBao9H5fcMH5wpcz3X+558uybXP3+n+oonlX0jd"
    "vaPtPtp3Ft3QLX6JptnWpRoUeOU+BSowk1mTbfOT6nqj9zzTfZNrueX+38/9XolcTmp2mpd+GJcz0seEf3Qb/DBpb/8AcdP9dVPd"
    "+EkeEP3QZ57YNL/eOn+uqHk8K/8AYRUuR5tAeAa5H1eCD7R6Fn/GE0HP/Q3f6iR+i0WuFe4/Oj0LefpCaB/3N3+okfoxFYin5Hy/"
    "GP76+H3KifCvTmWPR/1H/P7T9YeE+zh/+cPbf772n66B7t9Ob/i/aj/n9p+sPCPZt/hE21++9p+ugd/Cm/RZfP6ClzP1hgsuT/GZ"
    "ra1qdjouk3eq6ncRtrKzozr16sk8QpxWZSeOfJI2YPCl+Uzpvbf7fZDvFSfL7hXn6mR89COqSTLOAXpD9jMv+fmnf6Kt/UD+2F7G"
    "l/z907/RVv6h+adTPFyfcTmXiz6FcFpd8n5EamfpevSF7GX/AM/NN/0Vb+odH7e+23ss1/sc3RoujbxsbzULzT50rehCnVUqkm1h"
    "LMUjwRl+LE2/Flw4PShJSUnsLUzf0Wf+3tlJPl9KpP8A8aP1xpPKb8WfkZoS/wBu7Dw+k0v56P1ypfVfvOXjfOHzHE43di/8m9SX"
    "/sdf9XI/JPuj+Sv0H62bueNtak13WVf9XI/JPuX5K/QVwT/f8gmGAEB9AQNdT3j+5/c+x/UF/wC/K36qkeDe894/ufn+CHUf38rf"
    "qqR5XGP/AF/mOPM9IYwdL3p2sdnmzNYWj7n3TZ6ZfulGsqNWFRvglnD9mLXPDO6ya4Wfn76espPt1gs9NHtv01DwrC2jc1dEn3Fy"
    "eEesP7YTsck0lv3TPjCqv/sO97V3Lt7dOn/dHbutWGq2ucOra141FF+Dx9V+Twfktl+LO8die/8AVezztB03XdPuJwoOvClf0VL2"
    "Lig5JTjJd/J5T7mkz1avBIqDcJbkKo87n6kvCR5n9Ojs2tdc2O9+afbKOraIoq6nGPOtaOWGn4uDakn3JyPSVGaqQUoyzF80/Fdx"
    "xW+NKo6ztDWNHrRjKnfWNe3mpLKxKnJHi21Z0asZo0ayj8nOHHJoeB90U+uFkMH3yXQ5GwQ8FJDUS0iWyUilEuMSlE0SIciFEpIt"
    "RMkYGigZuZjUS1DmZFAyRpmkYGUqhjjEyQgZYUsmeFF+BvGmzCVVGvGmZoUm+42qVs33HI6bpdzeXMLa1t61xXm8Rp0oOc37kuZ0"
    "xo97OSpcpHGU6D8DZpW2ccj7JtDsA31rNKFxf2dvoNo1l1dRqcEsf92sy+eD6RonYx2b7eUamu6pe7juY9aVJ+ooZ/g+01/COWpx"
    "K0pPSpan0jv58vFnLWruC1VGor3/AG5v5I8zaZo95f3ULWxtK91XlyjSo03Ob9yXM+p7U7A976moV9TtrbQLR83V1Gqoyx5U45l8"
    "8H3ex3BYaFauz2voenaNRxj+56KU375dX8TiNR1W8vajnc3NSo34yOeXELqptSgoL37vw5LzPIrcUor2cyfgvv5I4jReyPsz2+oz"
    "1i/vty3MetOD9RQz7o82v4R2623BbaRauz2xpFholvjGLWjGMn731fxOsSq+ZEq2O85ZW0q29eTn8eXgtvI4KnErie0HpXu+/PzO"
    "UvNSu7uo53FxUqy8ZSyazreLNF1hOsdEaKSwkcqi28s3nWQnXfice63mL13PqWqRoqZyP0h97D178TjvW5GqjDsjVUzkPXPxGqr8"
    "TRjMzQbZLgkaqBuRqMz0m5PC5mC1ozqySSZ2vTNEpW9qr7U60bW27pSXtT8orv8A0HHXrQpLc66NCVR4ijT0fTLi7rRp0qcpyl0S"
    "RyeratoW1Ldu4qU7y9j/AIuMvvcH5vvfkvmdW3h2jUbS3qadoVNUKbXDKSeZz/Kkv0LkfKNQ1K4vazq16jk359DW04PXvHrr+rHp"
    "3v4nWpwo7U95de5fBd/z8Dtm8N8anrtw+OtKNJcopcsLwS7kdVdTiecs0+IrjxzzhI+qoWlO3goU1hHO1KctUnlmzxcsnbdt6Nb2"
    "tvT1bWqampLitLKXWp4TqLuh4L7Xfy649A0ejplCnqes0Y1LmaU7WxmunhUqrw71Dv6vwNmvcVru4ncV6kqlSbzKT7zz7m47TMKb"
    "273+y+/gezYcO1YnNG/cXVa9uZXFebnOT+XkbFsjQt+45O1WTy6iUVhH1VChg5GyhxYOZtKWMcjQ06GWjsFrQbxyPGuamD16VLY5"
    "PSmrKyuNRkudGGKfnOXJftPKXpJ7hep74jo1GrxW+jUvUSw+TrzxKq/evZj/AAWemu0LWrfa+1qt7cYdPT7eV7Vg/t1HypQ+LcV/"
    "CPCmpXde7uq11dVXVuK9SVWrN9ZTk25P5tno/pq31Tncy7tl+fD6nFfzxFQXfv8ALuNStJ5Neci6ksmCTPp5vc44LANi4hMRkzoi"
    "XGRkjIwouOSonTBm1Sng5KyrOLXM4mn1RuWzw0ddKTR6VvNpnfNr3rhWhzPS/Y5O31nR7zQr6KqW17QcJRfj3P3nkzRazp1YvPee"
    "j/R8v3LV7WmpdZY/Meb+paTqWTqLmt/A+jlJ1bOeOaWV8VufGO0bRJ6Nrt5YVI4lQrSg+Xg8HQL2GG+R9+9Jq0p0983s6aWZ8M5e"
    "9xTPhGoRxJnrWVd3VlTrPm0gu32tONT/ACSfisnDVo8zXkjcrLma00YVI7nz9WO51waADwsHmAJoYmS0BLRLKYmZtEsliKEzNok9"
    "legd2iq80S87PdRrZuNPUrvTeJ/WoSl98pr8iT4l5Tfgeh94772hs+iqu59xabpKkswhc11Gc/yYfWfwR+X+2de1nbWs0Na0HUK+"
    "n6hb8Xqrii0pQ4ouL68uabRy2mbR7Qt63c9Ssdv7h12tXfFO7VvUq8bfe6j5P5nzt5weE6zquWIv6mbR7jr+k/2PU7h047gu6yTx"
    "x09NruPz4T6BsLtF2ZvqhUq7V3BZ6lKklKrSg3GrTT75U5JSS7s4wfn0uwztdjT9Z/sB1nHX6sM/LiyZti6D2m9nfaHoevVNq7h0"
    "2dtfUlOdSxqqE6cpKNSEpJYcZRbT5nNV4XaOH9Kp63xQsH6T8p9eh5C9Pbs7s6NCy7RtNt4U69WtGy1NQWPWNp+qqv8AG5ODff7P"
    "geu4Qayu7J8q9LWwpXvo/bsjUSbo21O4g/CUK0JL9H5zyeH1pUriLXXHiI/N6EZTmoRjKTbwlFZbfgfop6LvY/Z9m+zqd5qFtCW5"
    "tTpRqX9aUcyoxfNW8X3KPLi8ZZ7kseP/AEVNt0Nz9um37S7hGpa2lSd/Wi1lNUY8UU14cfAfpJFYjyfmevxy5axRi/exsPqnXd5b"
    "82ds+nCe6Nx6ZpPrFmnC5rqM5rxjH6zXuR1r0jO0b+xn2Z3uvUI06mo1ZxtNPpz5xdeaeJSXfGKUpNd+Md5+bevazqevaxc6vrF/"
    "cX9/czc61xXnxTm359y8EuS7jg4fwx3Sc5PCEfpptXtc7Ntz30bHRN6aPdXU3iFD13q5zfhGM0m/gd4eGs5PyF45p5T6cz0j2R+l"
    "RrG09hXGh7h0+43Df2yUdKuKlfh9jDzCtN5lJR5cLWW08N8kzoueCyis0Xn3Aere3PZW3t+dnmo6RrtW2tI06brW99WkoqyrJPhq"
    "uT6Lul4xbR+ZlDS7y61uGk2UI3l3VuFbUoW8uJVajlwxUGuqbxh+Z23tT7WN8do925bj1eUrJS4qWn269XbUvDEF9Z/jSyzvvoPb"
    "Zhr/AG10tRuaSnR0SzqXyysr1rap0/k5OXvid9tQnYW8pVHnvwI9cejx2U6b2XbLpWMY0q+tXUY1NUvEudSp+BF/9HDOEu/m+rPp"
    "jkl1COUuh8c9LDtNu+zfs59dpE409c1Sq7Sxm0n6n2c1KuH1cY4x5yR80lUuavVsZ3vefaLsbZ9RUty7o0vTK7WVRrV161rx4FmW"
    "Pga+ze1Ds+3fdfRNu7u0rULrut4VuGq/dCWJP4I/Lq9vbu+vK17e3Na4ua03OrWqzc51JPq5SfNv3mOjcVqNaFajVnTq05KUJwk1"
    "KLXRprmn5o91cDho3m8iyfr03yyj4n6XWwNB3h2Y3mp31zY6bqmj05V7C+uakaUc4zKhKT7p4wl3S4X4nwzafpca3o/ZrT0vUtIe"
    "s7nt5OlRvripw0alLHszqpe1Koujxjiwm3nJ8K7Re0TeHaDqiv8AdWtV71wbdGh9ShQ8oU17Mff1fezmteF14VVJvGAbOT9HrVNP"
    "0btq2nqWqXlCysrfUIzrV7iahCnHhksyb5Jcz9CodrfZc4JrtC2x0/6zpftPy4yPifiz1Lvh0bqak5chLY/Ub+y92XN4/sh7X/lO"
    "l+039D7Q9h67qdLS9F3hoWo31ZN07e2vqdSpLCy2op55LmflppNhfarqVtpum21a7vLmpGlQoUo8U6k28KKXe2fof6MnYvadmO3P"
    "pmpQpXG57+mvptxF8SoR6qhTf4K+0/tNeCR495YUbWGXJ57kPJ9lXTxyYbydOjbzq1akKdOEXKUpySUUlltt9EvEuXso8XemP27f"
    "datd9nW0L1PT6bdPV72jLlcTT50INfYT+s19Z8uieeG1tp3FRQiDeD4n6Rm4dJ3T227m17Q7pXWnXN1BUKyi0qihThByWe5uLw+9"
    "YZ6r/c9Gn2Ta5ju16p/q9E8J9/Pme6/3PPH9iXXMf9fVP9Xonv8AE4dnaaOmCVzPSsk2fG+2n0ftvdqe6LfX9X1vVbGvQs42ip2q"
    "p8LipSln2ot59pn2UlvHVpfE+bp1Z0paoPDLPMT9DTZP/rXuL+LQ/qEv0M9lS6bs3Ev4FD+oensp/aQ8xXevmdH+oXP+bFhHwrsp"
    "9GfbXZ3vey3Xpu4dYvLi0jUjGjcRpKEuODi88MU+jPu0XhJC403hMaOepVnVeZvLGfC/Tl/4v2p/59afrUeEOzf/AAibb/fe0/XQ"
    "Pd3pzf8AF/1L/P7T9ajwn2a/4RdtfvvafroH0PCl/wCLL4v6ES5n6vw+1+UziN7aDHc20dY2/K5dqtSsa1o6yhxOn6yDjxYys4zn"
    "GTmIY9rP4TKfQ+bTcXlFnkVehVacXtdolz/JEf8A8g5ehTZY5dolzn96Y/8A5D1tlfhL5jcl4r5nauJXKWNXkvsLSjyLD0KrXv7R"
    "Lj+SY/8A5Dzt29dnlPsy7Qq+1aeqy1SNK2o1/pEqCpN8azjhTfTHifqE5JLqj89fTnee3295/wDJ1p/MZ6PDLytWraJvKwTJJHxb"
    "Qv8Afuw/zml/PR+uVL6rPyN0P/fmx/zml/PR+uVH6rFxxYlD5hA43dv/AAb1L/M6/wCrkfkm+kfyV+g/W3dn/BvUv8zr/q5H5JP7"
    "P5K/QVwT/f8AIJgCENHvpGYd57w/c/OXZFqX7+Vv1VI8HnvD9z8/wQ6j+/lb9VSPL4wv/H+ZUOZ6Qlzi/cfn/wCnpy7dI+ej236a"
    "h+gLSwfNO0XsQ7O+0DcP3e3PpVzdX6oQocdO9qUlwRzhYi0u9nhcOuo21bXLlguSyj8ysM7b2R7L1PffaBpO3dNt51HXuISuJpPh"
    "oUIyTqVJPuSWfe2l3nuWHotdjUZJy29eySfR6nXx/OPpmxti7R2Rp8rLaug2Wl0ZtOo6MPbqNdOObzKXxbPXrcbp6GqaefeQqb7z"
    "n6MIQpqMViKSST7kuRw++NWpaLtHWNYryjGlY2Fe4k5Pl7NOTOba7zzZ6cnaLb6LsZbFsLmL1TW+F3UIy50bSLy2/DjklFeKUjw7"
    "ShKvWjBd5cpKKyzwwlxKL78LJcYlKPMtRP0GMTz3MlRLUSox8jJGBqomUpmNRKjEzRp+RlhRz3G0aZjKqkYIw8jNCm33GxSt2+45"
    "Cy0yvc14ULehVrVpvEKdODlKT8kubN4Uu9nNOukcZCi33GxTt34H2DZfYB2ha/CFetpcNGtHzdfUp+q5ePBzn+ZH1PQewbs/0GMa"
    "u5tcu9euY83b2v3ijnwysyfzRzVOIWtJ6dWp9Fv/AAvmzmq19EdU3pXv2/7+R5c03S7m9uI29rbVritJ4jTpQc5P4LmfV9ndgG/9"
    "bhCvd6fR0O0fN1tSn6t48oLMvmkeh9L1XR9tWjtNpbf07R6XRyo0lxy98ur+OTjNT1zUL2blc3VSfk5cvkYu+uqm1KCiur3fgtvN"
    "njV+MUI+zmT8F4vfyOtaD2IdnW3uGruLWb3cFzHm6NuvUUM+Dw+Jr+Ed1stb0nQbV2m1dB0/R6WMZoUUpy98ur+OTrNW4cn7UsmC"
    "dbwMXayrb15OXx5eC2PKq8WuKm0MRXu+/PzOV1HV728m53FzUqZ/Clk4+pXfVs1J1fMwyq+Z2U6EYrCRwbyeWbc6xhlW8zVnV5mK"
    "VU6I0jWNM25VjHKqarq+ZDnk1VM3jSNt1RetNVTDjK0G8aZsOpz6hxmumXDmwcTVUzYhPJljlmGlBs5OwsKtaSSizGpKMFlmsaZi"
    "oU5TeEc9oeiXV9XVOlRlN9XjuXi/A5ex0G2062heazV+j0mswpJZq1fdHuXm+R1fe3aPSt6E9N0qlChR6OnTeeLznL7T8uh5qqVr"
    "ufZ2yz7+5fc61aqC1Vdvd3v7HZ9U1HQdrW/HKrRvbyPf1pQfl+G/ze8+Wbu3vqOtXE3KvU4Hyy3za8PJeSOqapqt1qFd1birKcn4"
    "9EaXrGfQ2HA6dv8A1KnrT6v9glOU1pSwuhuTquTbbyTxmvGWTJF9Fzbbwkj2dOBRgZlJLm2dz0fSaWiUaeo6rRU9RklK2s5rKo+F"
    "SovwvCPd1fPkp0nTKe24U73UacKmsSXFQtpYcbXwlPxqeC+z7+mOdWrcVpVa05TnN5lJ822eRcV+29WHs9evw93v7/hz9qyscvVN"
    "G1OtWua869ecqlSb4pSk8ts2KJq0UbtCJwzwtkfSUaJtW65o5azjzRx9tBvBy9lT5o86vI9SjSOZ0uGWjuGiW8J1YuphU4Ljm/CK"
    "5s6vpdN8UeR2ut/c2iKnxKNS8lwJv7MFzk/cfN3ssvSu87GsLHU8++lnuhztLLQqc8VdQrO/uYp81Rg3GjF++XE/4CPN9WTyds7V"
    "NxPdO+tU1mEm7apV9VaJ91CHs0/mlxe+TOnzy2foNhaei2sKeN8b/H+OXyPnq9TtarkuXd8DFIlluPMWDZxZUUY2gSMnCVGBKgdE"
    "YmNRMkYmSNMyRp+RrGmddOmTTgbdCDTQqNLn0N23o5kuR0Qp7no0KO5u6bB8UT0H6M9vUr7pt1h8FKMqkvcl+1o+IaJZudSOEem+"
    "xKyp7Y2NrG6rmPC40nGjnvxz/PJxR536krKlw+VNe1LZfF7HvSi6VpPHOXqr4vY+V+kDqcb3fWqyhLihCu6a/gpR/oPjF/JOTO3b"
    "yvp3V/Wq1JcUpzcpPxb6nSryeWz07ekra1hRXcki75xpxVNckkvDY0a76mrPqbFV5NabOacj5yrLc4FpCwVjkI8Zo8/AsCZQmiGh"
    "EMTLwSyGiWSwjFyaik2+5JdQZ330etMtdY7bNo6feQU6E9TpznFrKlwJzSfxijmrTVOnKb7kS9j1F6N/o5aJoOlWe5N82FPUtdrQ"
    "jWp2VxHioWKfNJxfKdTHVvKT5JcsnpCnTp0qapwjGEIrCilhJeS7hUm3BN9WfHfS931r2xeyh3m3qs7a+1C9hYxuoL2reMozlKUf"
    "CTUOFPuznrg/P5VK19XSk934Ix5n1y4uLOhPhq1qFOXhOcYv85dCtRqr71ONRfiSz+g/Je+vry+uZ3N9d17qvUfFOpXqyqSk/FuT"
    "bbOe7Nvu3d720TTtFub2N1dahQpU4UK04uTc14PpjLfkmexL9PYhq7Ty/kek/VFPKyj5n6UfPsD3n+9r/nxPpEG8tp8ss+aelJl9"
    "gW8/3uf8+J4Nt/eh8V9SHyPK3oG+pXbXdesxxvRrj1efHjp5/Nk96xfsn5s+i1uSjtfty27fXdRU7S4rTsa8m8JRrRcE35KfAz9J"
    "4JOOcYPR43TlG4TfeinzPKv7obC5e0tqzWfoy1GuqnhxukuH8ykeLkuR+n/b32eUe0vs4vtuOpCjd8UbixrTXs07iGeFy/Fabi/K"
    "TZ+bW79ta5tTXbjRNw6bX06/oSxKjVjjPnF9JRfdJZTPU4LWhKjozugRwwuhcYSnUjTjFynJ4jFLm34Jd56e7HvRUutz7DutW3fe"
    "X2ganecMtLoqmm6MPw69N83xZWI5TSWXzeD0bi6pW8dU2B5ePVf7nZwLdW7k8cf0C24fd6yef6D452tdiu++zWtOrrWm/StK4sQ1"
    "OzzUt34cT6035SS8mztvoS7np7e7bbaxr1VChrdpUsMyfL1vKdP5uDivyjlvHG4tJSpvOwj9B02+48dfui8bv6dsuTUvovqrtR8O"
    "PNLP5sHsSPFhM+Uek92Y1u07s6nYac6cNasKv0vT3N4jOeGpUm+5Tjyz3NRyfMcPrRo3EZy5AfmywRyGt6RqWiapX0vVrG4sb63m"
    "4Vbe4puFSDXin+noa9nZ3V7eUrOzt61xc1pKFKjSg5znJ9FGK5t+4+1ysahGBiZ6y2b6ItbVOzKFzr2q3GjbtuJOtTpYVShQp49m"
    "lViubk+rcX7OcYeD4L2pdlG9+ze89XuXSJwtJS4aV/Q++WtX3TXR/iyw/I5ad9QqycIy3EdHHCE5zUIRcpSeEkstt+Qo4yexfQ37"
    "CVRVn2j7vs/vzxV0ayrR5wXdczT7/wABPp9bww7q5hb03OTA7X6I3YW9j2FPeO6bb/ylu6X3ihNf73UpLp/3sl9Z/ZXs+J6MUlFc"
    "y8JRwj4D6V/bhR7OtHe3tv3FKpuq+pZg8pqwpv8Axsl+G/sxf5T5JZ+R/q3lbq35D5HWPTI7dPuDaXHZ/tG9a1evDg1S7pS52lNr"
    "+9Ra6VZJ839lPxfLxH1ZluLmrdXNS5uK8q1arNzqVKk+KU5N5cm3zbbecmN4X2o/M+stLWFvTSj8yc5BI90/ueix2Ta7j/r6f+r0"
    "TwtH5+490fueeX2Ua9y/5en/AKvROXi//rP5AuZ6V59x5K9MztV37sftH07S9rbjuNMtKulQrzp06dOSc3Umm/ai30S+R64XQ8H/"
    "ALoN/hg0v946f66oeJwuEZXCUlkpnQ36Q3bJnlvq+/0NH+oEvSI7ZGsf7Ob5f/Ao/wBQ+VAfUei0P8F4Ik9Seiz2wdpO6+2fSNE3"
    "Duu81DTq9K5lUoVKdNRk40pSj0inyaye3FnC9x+dHoWf8YLQv+4u/wBRI/ReL9le4+a4tTjCulFY2+5SPhPpz/8AF/1H/P7T9YeF"
    "Ozb/AAiba/fe0/XQPdnpyrPo/al/n9p+tR4T7Nv8Iu2v33tP10D0uFf+rL4v6Ey5n6vx+1+Uzq3a7qF3pvZfujULCvUt7q20e6q0"
    "atOWJQnGlJqSfc0+Z2mH2vymdT7ZKFe57Kt129tQqVq1TRbuFOnTg5SnJ0pJJJc234I+dpf3I56otn50S7Ye1Pi/wgbjXL/Lpi/s"
    "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"
    "7+R6FOxaeD51RtX4HI2dm3Jcjn6eiVIv6j+Ryem6LUnUSUG/gdLqU4LOT1Lezae5vdn+36+papb2tCk51Ks1GKx3s+u9vGsW+3Np"
    "6fsvT6ixCmqlw1+ZP3vMvkcn2U6JZbV23c7u1SHCqVNqgn1fdy82+S+J8C7TNx3Gt63d39xPNStNyfPkvBLyR8tTk+L8T1f/AB0v"
    "OX8G2VVr5/2UvOf/APK8zpGsV3OpJ5OvXMub5m/e1ctnF13nJ9FXnlnk3lfVJmvUka8nzMtR8zDI4Js8SpPc4cBgefgywS8CY2Jk"
    "MQmSymJmciWQdg7NtwPam/dC3JwylHTr+lcTjHrKCl7a+MXI4Bkt46dTCpBTi4y5Mlo/WjSry0v9Ot72xrwuLWvSjVo1YPMZwksx"
    "kn4NNHFb+2loW99sXe3Nw2jubG5Syoy4ZwknmM4S+zJPmn+lHh/0ffSH1fs6tae39btaus7cjJulTjNKvZ5eX6tvlKOefA8c+jXQ"
    "9U7c9IXsj1i2hVW77Wwm1l0tQhO3nH38S4fk2fBXPDLm1qZim13Nfmxg1g+R3/oY6ZO8crDfV9Stm8qFewhOaX5SlFP5I+rdi/YD"
    "svszvPuta/SdW1rhcY315w5pJ8mqcI8oZXJvm8cs4OQ1ft57I9Ot3Vq770mthZ4bWcq8n7lBM87dvPpTVdf025252f0LuwtK8JUq"
    "+qV1wV5xaw40op/e0/wm+LHRLqbQXELv+m8496wHM9qNJLkj5n6UDX9gPef72v8AnxOhbR9Kbs1t9r6XR1W51iOoQsqMLqMdPlKK"
    "qqmlPDT5rKfM6924+kV2bbs7Ktxbd0e41WV/qFm6NBVbCUIOXFF85N8uhhRsLmFaLcHhNd3vJZ4ybaqZTa58sPB+hXoq9sVr2h7U"
    "paRqt1GO6NNoqF1CUsO6px5KvFd+eSku6XPo0fno3ltm1o2qalo2q2+q6TfXFjfW01UoV6FRwnTl4pr/APrPp+IWcbunjvXIpo/W"
    "5yXccLufa+3d0W0bXcWh6dq1GP1YXltGqo+7KyvgeVuyr0vZ0bejp/aJo9S4nHEXqenRXFLznRbSz4uD/gn3PRfSA7INTpQnS3tp"
    "1s5LnC7U6Eo+T44pfnPk6thdUJey/iv4Edl212a7B21dK70HZ+iafdJ5VejZwVSPuk1lfBnaccJ851Lt27I7Ck6tXf2iTilnFCs6"
    "0n8IJs+U9o/pfbWsbWpb7J0q71m8aahcXcHb28H44+vP3Yj7yYWlzXljS38f5EfX+3btD0Hs82Hd6rq6o3NevCVGysJ4bvKrX1HF"
    "9YLrJ9EvNpH5nLU7ylrS1e3nG1u43H0mnO3gqapVOLiTglyik+iXTCOV39vLcm+dwVdc3NqdW+u58o55U6MO6FOC5QivBe95fM68"
    "fUWFh6LTab3fMD9J/Ry7XdN7UNoQqzqUaGv2cIx1SzTw1Lp62C76cuvk8p92fq3cfkztPcetbV1231zb+o19P1C2lmlWovDXimuk"
    "ovo08pnrTsy9MHTK1vSst/6LXtLiKUXfabD1lKfnKk3xQ/guS8kePfcInCWqjuunegPSW69m7U3VCMNx7c0rVlFYg7u1jUlFeUms"
    "r4MxbT2FsvadR1dubX0jSq0lh1ba1jCo14ceOLHxOr6V29dkOo0FVpb70ijy5xuZyoSXvU0iNW7f+yDT6bqVd96VWws8Ns515P3K"
    "EWeZ2Vwlow/huGUfTn7PNHxj0re1PSdhbCuNNUbS91zWKMqNnZVoRqRUXylXqQfJwj3Jr2pYXc8fNO1L0wNOp21Wx7PtIrXNxJOK"
    "1DUYcFKHnGknxS/hOK8meRtz65q+5dbuda13UbjUNQuZcVWvXnxSl4LwSXRJYSXQ9Ox4TUclOqsJdwZO8ejNoWl7i7ctsaXrFnTv"
    "LGpcznVoVPq1OClOcVJd64optdH06H6Y0o4pxx4dx+YPo/bq0zZXa7oG5danXhp9lVqyryo0vWTSlRnBYj385I9kQ9LDsjUUvpet"
    "cl/1ZP8AaVxehVqVVoi2sAmkfeU/FHDajtPa2pXVS71DbejXlxVealWvYUqk5PGObcW3yR8h/tsOyP8AyvWv5Mn+0X9th2R/5XrX"
    "8my/aeYrS5jygwyj6otg7Hg+WztvL/5ZR/qinsLZE+uztvfyZR/qnyz+2w7I/wDK9a/kyf7QfpY9kSX+69a/kyf7R+jXX+L8wyjz"
    "b6bWlaXovbP9E0nTbPT7f7lW0/VW1CNKHE3PLxFJZ5Lmfdf3PR57Jtc/f6f+r0Tzf6Uu/Nv9onactf25O5nZLT6Nvm4oulLji5t8"
    "n3e0j6P6JPbbsbs22JqejbmrahTurjVJXVNW9o6sXB0qcebT65i+R7dzRqysIxxvsLvPb0pYPCP7oN/hf0t/+46f66ofdJelf2SN"
    "/wC69b/kyX7Ty76WfaHtztI7QbHWdszu52lDTIW03cUHSlxqpOT5PuxJczi4ZbVqddSnFpA2j42PAhn0wj7R6Fn/ABg9C/7i7/US"
    "P0WivZT8j8yPRv3fo2xe1vStya/UuIafbU7iNSVCl6ySc6UoxxHv5tHr9elj2RpJfS9a/kyX7T5zi1vVqV04xbWBppGX05Gv7X/U"
    "/wDPrT9ajwj2c8u0Lbj8NWtP10D0x6T3b32f9oHZPebc27X1Od/WurerFV7J04cMJ5ftN+B5d2fe0NM3bo+pXbmre0v6FerwrL4I"
    "VIylhd7wmdvDKVSFtKMo4e/0Jb3P1qpvnJfjMts+Cr0r+yKOf7s1p5ef97J/tGvSx7I31u9a/kyX7T5/0K4/wfgXqR93w/F/Mfz+"
    "Z8H/ALbHsi/yvWv5Mn+0P7bDsiz/ALr1r+TJ/tD0K4/wfgGpH3d8+9/M6v2tcuzHdC4pJPRbzv8A+xkfMP7bDsix/uzWf5Mn+06/"
    "2g+k92XazsnXdKsrnWXdXmnXFvRUtOlGLnOnKMcvPJZaKhZ11JZg/AWpHiTQ5f7dafj/ACij/PifrfRTccs/I3Sa1O31C0r1M8FK"
    "tTnLCy8Rkm/0Hv2PpYdkcc/3XrXP/wB2y/aezxmhVquDgm+ZMWkfeeFd4fP5nwb+2y7I/wDKta/k2X7Q/tsOyP8AyvWv5Nl+08T0"
    "G4/wfgVqR95+L+YuHDzmXzPhC9LDsj/yvWv5Nl+0T9LLsk6fSdb/AJNl+0PQbn/B+Aal1OqfuiMl/sB2ysv/AH2n3/8AYyOR/c/J"
    "f+aPVEu7XKv6mkfKPS67Y9ldpu1tF07a9XUJ17O/lXqq4tHSSg6bjybfN5wb3omdtOxuzbYV/o+5q+owu6+pzuYK3s3VjwOnCK5p"
    "9cxfI9h21Z8OVNQec/uZ6lrye2pJ4fuPA3p1xX9nNPx0e1/TUPQkvSv7Jcf7q1t//LZftPKnpPb50LtD7UP9kO3Z3U7H7n0LfNxR"
    "dKXHBzzyb6e0hcGta1K51Tg0sMmvJOGzPl8UZqcMk01k7f2YbK1bfm8bHbWjqEa9y3KdWovYoU4851JeSXd3tpd59bmMYuUnhI86"
    "TbeEdeoW7nhJZbeF5s+m7H7Du0bdUadaw23cWtpPD+lX7+j08eK4vakvdFnrTs87NNi9nFtT+5Wl09Q1aEcVdTvYKdaUu9x7qa8o"
    "497Oz3muXFTPFUaXgmeTU4xUltbw+b+38nn1rmhSeJyz8PufEdo+i5t/TlC43puereVVzla6dH1UPc5yzJ/BRPrW2tI2Tsyj6ra+"
    "2LCxmlj6RwcVaXvm8yfzMF3fOTfM424upPvOWUK9z/em2unJeCPJr8YlH+0lHzfi/wBjnNU3BdXLkp1WovuXJHA3V63l8WTRr15P"
    "vNKpWfidtC0jBYSPBr3dSq8yeWbNxct95o1bhvPMx1ajfeatSTPRp0kjjbbMlWs8mtOpnvFORhmzqjBAqeRzqGGc/MU2YpM3jE0j"
    "SCUzDORUmY5ZNoo6I0iZMlsbQsGiN40yWS2Xhi4cjybxpEc8jSz1MkabM0KLE5I2jTMCh5GSFNvuNqlbt4wsnM6NoN3f1406FGdS"
    "UnhKKOercRprMmdMKLfI4i1tZVJJKLO37c2lXvKTuq8oW1rT51K9V8MI/tfkjmY6foe2KTnqcoX1/FZ+i054hTf/AGkv6EfON99p"
    "lxcVHRo1YVFT5U6dNcNGl+TH+lnnU53PEJaLZYXV/t9+XxOvsIUv7nPp9/zwO7a7u7R9rWsqGjYjPGJXtWP3yX/dx+yvN8z4vuze"
    "N5qdaoqdScYTeZNyzKfm33nXNV1S5vriVa4rSqTk+9nHSqNn1PDOA0bX15etLvbJlKVTZ8uncZqlaUnltkcfmYc5GsnvKKQKBmUi"
    "osxRNzS7K71K/o2Fjb1Li6ry4KdKCy5P+hd7b5Jc2TNqKy+RShkyWFvcXl3StLWjUr3FaahTpQWZTk+5I+iWNpa7RtZU6NSlc67U"
    "jw1riD4oWqfWnTffLuc/guXWLe1s9pWk7OxrU7rWKsHC7vYPMaSfWlSfh4y6y8lyONi3KWXlt9WeDcV3dbLaH/2/j3d/eejbWmHl"
    "lpynJyk22+rZnpR8iKcTZpROecsHtUaRlpRNyjDn0MVGBv29M46kj06VMzWsPI5a0p9ORq2tLocvZ0unI8yvUPRp0zcsaPNcjs2k"
    "W+XHkcXYUM45HbNBt4+tUqnKFNcc35I+eva+EzeTUI5MG99Xs9ubduL68a+j6bazvbiOfrNL2Y+9vC/hH5+a1ql3qmqXep31R1Lu"
    "7rzr15eM5ycpfnZ6T9L3dk6O3bTb1KrivrFw7q5SfNW9J+xF+Up4/wBGeWKs3nqfUfpm1dvaurLnL6L+c+CPn76bc1Dp9XzMjrvu"
    "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"
    "fZpTjoW340KsKcUpU9AsY1KcfDiqezGT8ebfidl0q57KvSA2Vc1VYUdSt6cvUVlcW3qruzm1lNS+tF45pptPz5o6NvfbXo0dklGx"
    "0zcm37Ord3NL1lOFahVvbicE8Ocnn2VlNdyznC5Hc/R41Hsj1Kx1y47K9NVjT9ZRjqEVbVaKcsT9Xym2unF9X4nDVhTVLtaUZ5/y"
    "fIN8nhDtM2Rd7Q7UtU2RSc72tbXkaFq8YlXjU4XSePGSlH45Pa/ZJ2M7B7Idmvce6oadcavb2/rtR1S+ipU7Z98KSkmoxT5JpcUn"
    "70j4r2m/Q4+nrpTvlH1P3U0zPF04vVQ4f/Fwn2H056WoVOwutKyjUdCnqlrO94eipZkk35cbh8cHbc3FS47Kk3hSxkSOT0b0h+xv"
    "curx27PUpQjcy9TCeoWDp21Rt4SbksJP8ZJHnj00dh9nu1tetb/ad/p9hql1Uav9CoTz6tNZVaMVypLPJxeM5TS6nnbglxYSbeem"
    "DY1CneUb25palTuKd3HProXEZKopY+0pc8+89CjwuFvVUoTaXTqDbPX/AKI3YLoc9s2W/d6adT1G6v167TrK4hxUaFHPs1ZRfKU5"
    "dVnKSxyy+X0vVPSK7GtB1uW3fupKUaE3RqVbOwlO1ptPDXFFYaXjFNHZ9T+k1fR7uFt3M7me1mtP9T1cna+xw47/AAPzGUJPhwn0"
    "WDzbW3/1Cc5VZPbkht4PZfpdbO7KNS7P4b30vVdE0nWq9JXGnztpRjHVoP7PBD6zx0mlyfKTx00/3PzS7C923u6peWNrdShe26g6"
    "1CM2vvcunEnjuPJF1b6hSt7WvdULmFCvTf0WpVhJRqQUmnwN8mk89OWcnsT9zweNsbwfhfW3L/4cjovLZ29jJa2919RZ3Pk3pXbK"
    "3Fc9umv1tF2rqlaxkrf1c7TTqjpPFGGcOEeHrnp3nxTVdL1LSrj6Pqmn3djWxlU7mhKlL5SSZ7r7XfSctez/ALQtQ2jPaNxqErL1"
    "ebiN/Gmp8cIz5RcXjHFjqd8rWO0+3jsgtbu806TsNWtpVLaVeC9fZ1U3HijJdJRlF9HhpeDIpcQrW9KDq0/V23yGMnw/9z3sNPvN"
    "v7xd3ZW1xKF3a8Lq0YzxmnPplPwPknpnW9C17fNXo21ClQpq1tGoU4KMedGOXhcj7T+5921Swsd+2NbHrbfUbejNrpmMasX+dHxz"
    "02JJ+kDq68LSzX/+mJpatviU/h9hP2T6B+57aZY32qbyqXtlb3MadCzUfXUYzUW5VemU8dD7pvjtQ7GtlbkuNv7guNPtNRtoxlVp"
    "LSXPhUoqS5xg10aPk/7nlY1KWhbx1Nxkqda6tbeMscm4QnJ/z18z4d6W90rz0hN2zhLijTq06HXvhQgmvnkxlaq7v6kG8JLu+QZx"
    "E9u9qtlt+47F90anY6ZYOnV29c16NSNpCLxKg5RkvZynhpnkb0GbW0vO2yVG7tqFxTej3L4KtNTWVKlzw11PWm8+GPo36wu5bQn/"
    "AKoeTfQNb/s6f/Jrr9NMzs3izrIJc0fQ/Tg2ncazufs+0La+jUqmo6hK8pUqNtRjB1HmjzbSSSSy23ySyz6PsvYuwuwLsjuNT3Sr"
    "K7uowjV1K8qUI1JXFZr2aNGMl0zyiu/nJ9+PrGu6htbTNb0iprF1pdrqt3KdlpkricY1qjnwudOnnnz4Y5x4R8jzn6e2zd0apoen"
    "brsb6vdaJpUXC7sIr2beUnj6SsfWTyoyz9Xljk5HPb1pXCp20npj9dwaxlnlztZ3xfb/AN33Ot17O20+2ScLKxtqcY07alnKj7KX"
    "FJ9XJ9X5YR7s7a9I0mHo7bkuIaXYwqx0ByjONtBSi/Vx5ppZTPzoT4c8uiP0937t693Z2OantzTpUoXWpaTG3pSqyxGLlCKy34Lq"
    "elxVQozo42Sf2Ip75PEPoy9kVftN3r6y/pThtvTJxqahUXL1z6xt4vxl3+Ec97R7O7bNB0O17GN2K30jT6HqdEufV+rtaceDFN4x"
    "hcsHT+0LcW3vRu7FbXRNAVOtq1SnOnp8KiXFcXDWal1VXgm8v+DFeXb+1GvXvvR0165uKjqV6+151Kk2knKUqCbfLzZxXdxUuK0K"
    "vKGcLyyyopJNd5+abXPkMbWGGD7RI48jRUWSkUi0iWi0zJGRiRSNUZNGaMmZIzZgiZFFm0cmUoo7Js3em4dpXcrjQdTq2vG81aLx"
    "OjW8p05ezL34z5n2vaHbFt/cHBa7lox0G9fL6RT4p2c359Z0vjxR80edIQfgbFOElz5o09GVV5aw+q/Pqc1WnCXtHtbSpatovqtT"
    "0bUHCjWXHTrW9RVKNZeOVmM0dt03tC0y6xb7lsfo1V8vpdtFuPvlHqvhk8R7L3vuPaFWT0XUp06FR5rWlRest6v5VN8s+aw/M+xb"
    "S7T9s7jlG21qC29fS5cc5OdnN/l/Wp/wsr8Y8674Qqu9WOf+Udn+eKJpydLaD26M9Ow0221C0V7pV1Qv7aXSdGSZxN3p7i2nFpo+"
    "d2a1Xb9WF7pl3UoesSlCrQqJwqx7nlZjNfM7doXaVRuZq13Ppyz0V3ax5++UP2fI8Kpw+4petReuPn4d/wAvA6UqU9mtL8jYnYvP"
    "Qx/Q+fQ7lbWmnana/S9HvaV3Rf4Mua8mu74mq9MqKphwafuOKN73PZo29Dwdcp2WX9U3rPR51pqMKbbfRJHY7fSqdKm61zOFClHr"
    "KbwcNuLeenaJbzhZOMcLnUl9aXuXcTG4q15aKKyzohaJbyN2pp+maLR+kanNTmllUIvm/e+4+adoHaV9a1oziqUeUKFLlBe/xOo7"
    "135farUnTp1JQpN+PNnzy8rSqScnJts+t4R+nHlVbrd9OgqjwtMNjd3Brt3qdWU61V4fRdyOvVpNvqZKknk16jPu6FKNOOmKwjil"
    "Exzl4mCZlmYpHUjJoxvmS0XgEiyGRhlKOSuHvO2dnOyrvdl3VqzrKx0e0531/NezT7+CK+1Ufcu7q/PC4uKdvTdSq8Jfn4hKLbwj"
    "W2HtHUN1ahOlQnG1sbZKd7fVV97t4efjJ90e/wAlzPoOq3thY6ZHbu26MrbSaUuKc5P77d1O+pUfe/BdEuSNnXNRs6dhS0Hb9s7L"
    "RbZ+xTz7daXfUqP7Un5nAuOT5qrcTvJqpUWIrlH937/JfHc2hFLkYUmy4wMsYGSMBuR2U4mOMPIywgZIwMsKfkYymd9OIUoG1Spi"
    "pU/I26VM5ZzPQpRKo0+nI3qFPyMdGBv0KfQ4qsz0KUTLb0+hytnS5o1ran05HL2NLOOR5depsdsUchp1L2lyO16PRi5xcuUILik/"
    "JHCadR5rkc3duVvpKpU/77dzVOP5PefP3UnN6V3mFw20orvPg/pf7qdrtO30KjUauNcuPW1knzVtSaePdKfAv4DPJtV8z6D267qW"
    "7O0jU76jU47G2l9CsvD1VLK4l+VLjl/CPn1TmfpXDLP0OyhT73u/i/ssL5HztzU11G1yNeZODI1kIx5m+nJzpChEz0qeSqNJs5TT"
    "tPq16kYU4OTbxyOmjbuTOilTcnhGGztZTkkkz6LsLYtfVc3t5KNnp1H2q1zV5Riv6X5HI6BtTTtvWVPV91T9WpLio2cX99q+9fZX"
    "mzhN877vNVUbShw2thS5UbalyhFf0vzZrly9Wi9u+Xd8ur8l5Hv0KFO2jrrc+h2/dW+tP0XSZ7f2jF29rJcNe5fKrce/wj5HyTUd"
    "Tq16kpSm22cfc3k6ksuWTVlNt9RU+zt4uNPm+b738WYXHEJVHhcjZlXk31FGTZrReTatabnJJEqTkzljUcmb1hTc6iil1Z3aN1DQ"
    "NClUTSvLiPDT8YrvkcLpdvR063+nXfKK+rHvkzgtb1Wtf3MqtR9eSS6JeB0yxGOGenCsraGf9z5Gve3DqTbbyaFSQ5zyzDKRyTm5"
    "PJ5NSq5MGzHJjbIkznZyymJi+INktmbMXI1wH3AJo9shoXkZGS1yIaJZDJfkUxMzaIZDFJexP8l/oKZLMZIln6A7/wB77Pq9hGt2"
    "VtuvQat5Pbk6UKENRoyqSm7fHCoqWW88sH57pN9TLwrwXyFg8qw4bGzUkpZy8mSjg9ZegruLb2g7Y3LS1rXtL02dXUKMqcbu7p0X"
    "NKk02lJrKyfNfSZ3PZU/SXutzaHeWepUrSpYXFGrb1o1KdSVKnTlhSi2uqw/A+LP3EtLJnDhkIXMq6edSxjw+xOnc/RKeudmfb12"
    "c1NMq6vSdvdqFSrbfSo0byzqxeVmL6NPKzhxa8Uzpmz9q9hXYpuywu6u5lqGv3VdWtrK6vKVSVqqnsuo4wxGnFJvM5d2Uup4gfg0"
    "n8CenRJfA4o8FcE6carUH3fyTpPX/p17l25rmyduUtE17StTqUtTnKcLS8p1pRXqpLLUW8LzO3eiRvLaumdhWhWGrbn0Swu6Ve44"
    "6Fzf0qVSKdeTTcZSTWU8nhJPHRIH5pfIqXB4O1jb6nhPP1+4aTk911VW3ZqlanVU6c7+vKMoyymnVk00z3T6L+9No6d2HbWstS3T"
    "olndUaNWNSjcahSp1Iffp4zGUk1y58zwE3z5EuKfVL5G19w+N1SVPOMbiwd47PO0LUOz3tS/2VaXCNxCnc1o16DliNxQnN8UM92V"
    "hp9zSZ7Pq6v2K+kFtm2oaleWdatS9unb17hWt/Zza9pLmn3c8cUXhH578OA7sYz70Z3XDY3ElPVpku9CwfoBouxewXsaoXes3N3p"
    "0K9SjKk62qXkbqq6cliUKdPnnK5Phjl9M4PKzr9nW8PSL0unpegU9G2dealSo1barXdKM4c+Ob9r70pPnwp4ifKU8PlheaRDWeoW"
    "/DnR1SdRuTWMiwforuntC7Lexns8+h6Hc6TBW1KT0/SbG4jVqVqry1nDbw5c5Tk+merwj89Li9r3+sVdQvJqda4uHXqy8ZSnxSfz"
    "bNTC7kl7kPoFlw+Nrl5y3zYsH6E+kHvPZ2o9he6rGx3VoV1c1tL4KVCjqNGc5yzHkoqWW/I+U+gduPb+haLuunrmu6Xpjq3ttKlG"
    "8vKdFzSpzTa4mspcuh5L+CXwHnxS+Rzw4RCNCVHVzec+H2D3n6Cb22d6Oe8t03W5dxa3t671O74PXVFuVU1LggoR9mNVJcoo43tT"
    "7dezns32HLbewLvTdQv6Vs7bTrTTZesoWvJpTnNezhZbwm5SfvbPBbSz0XyHzwRHg0crtJuSXd3AFScqk3KUnKTeW31b8SJr2ZY8"
    "H+grnkTaUZe5/oPXaT5ifI/U2z1uz252VW+v6jGtK007RKd1XVKPFPghRjKWFyy8LofOdP7N/R031fLd2nWOhXzry9dUVC+lSpuT"
    "eW6lBTSi/FOK80dh7QK1CXo2aynUjz2jU5cXP/cqPzZq4c28J+9HynD7J3CnKM3F57hs9+dvXbztPs+2vW0XaN/Yajr8qPqLO3sp"
    "RnRsVjhU5uPsrhXSC5tpdFzPM/ondpun9n/abXvNxVZQ0zV7Z2t1dNOToy41ONWSXNrOVL8rPcfGuiwCePE9ujwujToyp5zq5sR+"
    "h3a12b9lfbBCx3Be7lp06lvQ9XTvtP1KjwzpZclGXFmLSbbzyayzF2M692IbFjqeytpbk06MrVRr317dX1PFzVlmKSqyajOUVHmo"
    "Lhimu9s/PXCfNqPyQfBYOZcGbh2cqj09yDJ9j9LDWrO69ILVdX0LU7e5hCFnOhdWlaNSKnCjDnGUW1lSXzR6d7HO3zYvaLteGiby"
    "udO03WKtH1F7Z37jG3vMrEpQlL2Wpd8HhrOOfU/P/GOiHnlg6q3DKdWjGlJ7x5MR+imndlnYHtTVYboo6doNpUoS9dSq3WpudGlJ"
    "c1KMZ1HBNd3Ll3HnT0x+1XZm97+y0bathZahOyqcdxrnqcVJ8sKlSn9aVPvbfJvGO9vzqor8GP8AFQPJlb8LcKiqVJuTXID1v6Jn"
    "pBaNpO37TYm+ryNjCz+96ZqVTPqvV5yqVV/ZcW/Zk+WMJ4ws/YtU7KOwXcepT3PX0nQLidWXrqla31HgoVW+blKMKig89/LmfnMu"
    "XQWOfSPyQVuEJ1HUpTcW+ePxBk9pelN2udm1lsGtsPb1pom4L2VNUKEKNGFW00yKWOOMlyVRLlFQfJ83y5PgfQM3Pt3QtC3XQ1zX"
    "tL0uVa7tpUo3l5TouolTmm1xNZxy6Hk3OUGF3pfI0/0mHo7oRk992xZ3yfoLvLZvo57x3Lc7j3Bre3rrUrvh9dUW5VTUuGKivZjV"
    "SXJLoa3aJ269mfZjshaJsa803Ur62t3b6bYadP1tGi1yUqk1lKKfPq5SfvbPATS7or5Dy+ncZQ4LHZVZuSXd3BqPW/oIbq0LStN3"
    "pU3Dr+madXurq2qxd7d06LqvhqcTXE1nm+ePE6F2/XG2d0ellaKd/Y3+h3d1plC6r0buLoypOMI1F6yLwsJtN55HwXr1SfwE4rwR"
    "0vhq7eVaMt2sfT7E52wfo9qG9+yHsX2DK10q80mhZ0FKdvpthcxrV7qo/dJybbxmcnhLv5H567s1m73JuTVdfvsfStRuat1VSeUp"
    "TblheSzj4HFxil0S+CLXIqx4dG11NvLfexSlk/Qrc29NmXHo96np0N26BUvJ7UlRVCOpUXUdT6LjgUeLPFnljrk8w+hXq+k6F2zq"
    "91nU7LTbV6Tcw9dd140ocTdPC4pNLLw+R8Sws54Vn3DceLrhk0uFQpUZ0lLOryE55eT1D6eG6dE1m72ZPbuvadqMrWN3Kc7C8hVd"
    "KTlRccuDfC+WV7j6f6O3blt/fOxami7+1TTbPWLOj9Hu3qFanTpahSknH1i42k21lTj48+j5eD1FLokvciuqw0viS+D05W8aMny5"
    "MXaNPJ9M9ILYeg7M3jKe1Nc0zVtv3/FVtPot9Trztn9qjPhk3yz7Mn1Xmme5Z9qnZ5o20fuhcbx0OpG0so1J0be/pVK0uGmvZjBS"
    "zKTfJLxPzPikuiS9yGoRznhjn3GlzwpXUIRnN+r345kqrpydt7YN/at2kb1vty6pmnGonTtLZPMbags8FNefPLffJtntTfW+dn3H"
    "o7apY2+6tCq309rulG2hqNF1XUdulwKKlnizyx1PACXkHq45+qvka3HC4VlTinhQ5eRCq4z7yWm2PBcY5LVJvoj1VTb5GDkkYsDU"
    "Tbo2Vap9Wm2vE2YWUIf36rFeUebOinaVJb4MZV4rvNCNNsywt5y+rFs30qEP73S4n4yMiVer7KWF4JYOuFku9+BzyuWaULVr68ox"
    "+JljTpR6ZkzmNP25qV4uKnbz4e+UuS+bOTjommWKzqF/CU11p0fafzO2nZNd2Dgq8RpxenVl9EdahTlJYhDHwN220i+rrijRnw/h"
    "PkvmcpU1fT7TlYWNNNdJ1fakcXqGtXd0/vteTj+DnC+R0dnSh7bMo1bir7McL3/b+TY+5lrb87q8hn8GmuJlK7sKC+8W3E19qo8/"
    "mODncSfeY3Vb6sj0yFP2EbK1nL25N+R3fbvaNubbv3rSr9RtHLM7OpTU7efvg+S96w/M+qbN7TNr7hnC31acdu38uWa03K0qPyqd"
    "afumsfjHnJ1Bqs10bPNuFCvJyezfev36nXSp6FhLY9pxoahpVzSurW5q21SUVKlWo1OU49zUlykvmj6Nsvel9UrQ0/W4UatecJOj"
    "US4Zyai3iUVy5468vceNfR83lrWnb60nbq1Kt9xtRru2qWk5cVKNScWoTin9SSnw844z35PSm3krPcVhcVX7UbmHG35vDz8Gz5ni"
    "VpCrGUKqTaWU+/8Aj4ZZ6VCTjhozb73zXu6koRk048oxX1Y+5HyvV9Rubmo5VaspZ8Wdg3xQdtrd3RX2Kso/JtHULnOXk97hVnRp"
    "Uoumj0qiNG5k5NmjV5m7VXiadXkfRUziqI1Khrz5GzUNeojsgcUzBIxyRlkicGyMGY+FjUeRkjHyO/dmmwPu/Seu65UqWO3beWJ1"
    "VyndSXWnS/Q5d3Rc+nPdXdK0pupVeF9fcurJUcmh2a7FuNzzq6jf1ZafoFpL+6rxrDm/+jpZ+tPxfSPvwjv2uapRlaUNG0a2jYaN"
    "aLht7aHf4zk+spPq2zb3JrKvaVDT7C2hYaTaR4LW0pLEYRX9JwDjk+Uq3FW8qKrW2S9mPT3vrL393Jd+TUuUTWccsOA2PVlKHijT"
    "WbQRghTMkafQzRgXGmZuZ3U0YowM9OBcafkZ4UzGUz0KSFSpm3RgKlA2qUPI5pzPQpoujA36EOhiow8jftqfNcjgqzO6Bs2tPODm"
    "bCjzTwaVpT6cjndOo5a5Hk3FTB0p4Ryem0HKcIRXOTwdO9ILdX+xnY+rX9tU4Lj1a06wafP11RNOS/Jjxy/go7/aYtbWtdv7EcQ/"
    "KfJHk70sNxyvN02O2KNRujpVH11yvG4qpPn5xp8K/hMXAbP07iEU/Zju/gvvsvmebc1cKUl8F+/kfC6qSWI9FyRryWTbqRyyY0W+"
    "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"
    "25UF6ya+2+nwRUaGFqm8I0UNsy2Qre0UYqrXl6uHn1ZVe/jCDpW0fVx733s0K9xUqyzOTbMLl5jdworFMrt1FYgZZ1HJ82RnJDDJ"
    "hqbMXPI2IGxBklyKyIEMRm5iDAwAlyJwJovAJDwZuRgDmPAFtH1hLRLRbJa5ENEshktFyJZlJENEMlop9RMyaM2QJovBLMmiWR0E"
    "ymJ9TNogloRTQiWhE4EyhNENEsnAkWJonSIkRXQRLQhYENhgWBMnyAYYFgQhYHgaFpETgMFMMBpESA8AGkCcBgrAAokk4HgYYK0g"
    "TgMcygwUoiFgMFYBIekBYDhKSY8chqIiMDSK4QwPSInAYLwNIpQEQoj4fIvA1ErQIhRGo5L4S4xKUCTHwjUDNGGTNToOXRGsaTZm"
    "2aqhkyQpN9xzdhoV1XgqtRRoUf8ApKr4V/8Av4HIQho+nfUhK+rL7U/Zgvh1Z3U+HyazLZHPUq6ThdO0i7vX94oTkl1ljCXvZya0"
    "vTrJZvLlVqi/xdHp8ZFXmq3d1H1fFwU10pwXDFfBGpGhUqS5ps7KdClDaKyzzatab5vCNmWpOnH1dlRhbw/FXtP49TV4a1eeZOUm"
    "znNC23e6lXhRtbapWqSfKMIttn0XTezyx0anG53Vf07JYz9GptSrS8sdEaVJKGFUl8lz+SR4V5xe2tds5l4tny/TNEurytGnRoTq"
    "Tk+UYxbbO+6f2cys7aN5uG6o6ZQ6qNR5qS90TmNQ3xpmiUJWu19No2UcYdxP260vj3HznX9yXuoV5Vbi4qVZvrKcm2VFTe+NC9+8"
    "vsvM8pVuJcQfqf049ecvsvM7nX13begQcNE0+FatHpc3PtP3qJ07cG7NR1KbdxdTmu6OcRXuXQ61cXkpZfE2aVSs3nmZyrwpvMef"
    "V7s9ay4FSpy1y9aXV7s3Li7nNvMjTqVnnqYZ1H4mKUvM4Kty5H0FO2UTJOpnvMTmyWyWzjlUbOpU0iuIWScjMnLJaiJsBsORA8CB"
    "AAAUikSil1LRLLjyPTHor6k7zs/1bSG+Kenakq0V4Qr0/wCtSfzPM8eh9o9EvU/o+/NS0iT9nUtLm4rxqUZKovjw+sMb2OaDfTf8"
    "+Q6bxI+971pSq7PsqmOdC5q0n5KSjNf/AHHzC6XNn2HWaLrbR1Ok1zp1aNZfOUH/ADkfIr6HDNo14LPMJR6P67/udVSeIo4qujSq"
    "rmzeuDSqdT6emefUqGpOPMxyhjL7jZccs7H2baFHXN32VpcQ4rKk5XN54epprikn+U8R/hGla4jQpyqS5JZOfOp4R9B7Euy51bGG"
    "7tz2KrUYpVLHTpLPH3xq1V+D3xj39X3I7huad5f3kq9xJt9Eu5LwRisNe1W21KvqNrUUZynxTpv6ko+DXguS8uR2qnRsty2srqwS"
    "o3cVmtayfNecfFH5hf3lxO5dxcbruxyj7v57+86KtHtKemH/AGfO6ltLPNGGVsztl5ps6c3GUMNHH1bNxN6d2mjzuyaZ1+VDHcQ6"
    "PkczUt8Poa9Sjg6Y1sm0InGOn5B6s3XS8iXTNFUOumjVUPIaibPqw4A1nfTRhjAyxiVGPMyQiQ5HoUiqcTbox5mKlE3beHNHNUkd"
    "9Mz28OfQ5W1p5aNW2p5aOYsqLbXI8yvUwdUTesKOcHP0aEo2KpxWJVnzfhE1NLt1KcY9cs6n28b0ltfYepVrSpGndXGLG0kuvrJ5"
    "4pL8mKk/keVTo1Ly4hQpc5NHNXm28LuPhfa9e2esb3v9Y1O74LWm1b2dGHObo0+SeO7ifFL+EfP9W3hUhaTstLpxsbdrD4H7c1+N"
    "Lr8Dreq6hUrSblUlJ+LeWcLWqybfM/aqNpTtaMKb30pJdNvcc9a70rTTWPqZb28qVJNuTZx1Sq22OrJvvMajKT5GdatKbPNlJyZi"
    "k2xKLlySNuFq0uOo1CPiynWt6H97h6yXjLoc7p98ngnT3vYx29pOazhRj3yfJGd1LW2Xsr10/F/VRpV7qpVftSbXcu5GCUm2Q68Y"
    "ewvmHaKPsm1c3tWs/bm8dyXJI1XJsx5Gmc0qkpvLZk5tvLKY8iGSmLUANgBYtQsjQDSKRDkCQ8AkNDIcgQYKDA0iHIQFJDSHgnUa"
    "zQsFMRo0faYIxz6EsyYJaM2iGiGiWi2SzNohkNEtYZkZLM2iGiCWUycGTRDJaFgtolozaJJFgrHMTRLRJPiIpi6EtEsTE15lYETg"
    "RLQimhEtCZLDA8AxaSSRjDAtIicCxzKwAaRMWAwPA8BpESDKwIekROAwVgMBpEIEhtDSHpETgeCkmNRK0gRgaRfA8BwlaGBKQ0is"
    "DS5FKIicBwlpDwWoBghIfCWlz7yoxKUBYMaiWomSMMmWnRcnyRpGnkWDAoNmWnRlLCSOWsNIq14+snw0qK6znyX/AOzkY1dPsI4t"
    "KSr1V/jai5L3L9p3UrJtZlsh9m8ZexpadoVapTVe4lG2ofh1OWfcurOQV1pmnR4bG3Vaqv8AHVln5R6I4+7vK9zPiqVJSfmzFCi5"
    "vxO2nGENqa+ZzVaij7Jkur25u6rnVqSm/Nk06Epy6ZN+w02rWklGDPqezOyu5ubKOra5Xho+l9fX3C9qovxI9ZfoCtKFGOuvLH7/"
    "AAXefO8Q4pSt08vc+a6PoV1fV4UqFCdScniMYrLZ9V0Lszs9Jt4ahvG9hp1HHErWOJXE/h9n4nMXm69vbStZWWz7FU6mOGeoV0pV"
    "p+7uivcfL9x7qur6tOpWrzqTk+cpSy2ZxdxcL1F2cer9p/svN/A+Tq3V5xCWKe0ep9A1jf8Ap2iWk7DaWn0dMo4xKtjirVPfI+Wa"
    "1uG5u606lWvOcpPLlKWWzhLy+nOTblk42tXbzzKiqNqn2a3fNvdv4s9Ww4HCk9TWX1Zt3d7Kbbcmzj61Zt9TFOo2zDKWThrXLkfS"
    "UbWMVyLnNmKUgbJZwym2dkYJClJ5JGxGTZpgT6iwPvAlhgSKQAIBdQ6FJZBoEgJwPAIY8CYIoSQ0WkSy4ncexnWFoPantrVJvFKn"
    "qFOnWef8XUfq5/mmzpyM1Nyjzg8TXOL8H3FumqkHB96wZ5w8n6B1rVu31aymucrSrH3yg1JfzT4vrNJRrzS8T7XtLUqevafomtRa"
    "cNVsqNaT86tJKX/icj5NuK0dG7qU5LDi2n70eTwOq1UlF89vHl+xrXl6p1KvFmpOD8Dlbim13GnOHPmfZU57HlVKhpqm2fWey7Tp"
    "6Zs261Jw/urV6vqaPLn6im+ePyqn8w+cafYXGoX9vY2ceK4uasaVJfjSeF+0+q7yv6WhaJKlZyxRsqEbGy82ljj/AJ0/ezyeMVZV"
    "FC2hzk/JcvPHgx0ZpJzfcfM96a/fU9x/StPu50Z2TdOhUpvz9p+DTeeT5NJHdOz3fMtZrUqaqx0/XafOEIPELjzp5+14038Mrkvk"
    "Op1+JtJnDSq1FPMZNNPKaeGn4nq1OD0bi3VNrDS2f36r3E0q8ovJ7V0PWbTcsVa3sadpqqWE1yhX93g/IxalplShNwqQcWj4R2f7"
    "6V/6rT9yXPqrpNKjqUpYU33Ks+6XhU/jfhH3rb+4I1+HSdxvhqx9mldS5PyU/wCt3/nPzjifC63DajUVt0/ddV7uaPUgo3Cz3nDV"
    "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"
    "jKWulJdP+z4dfUMNrBubO0WGp7gtqNaHFb0m7i484Q54+L4Y/E3L2z++tNd52/YGn0rPTat7W9j6VJ8T8KFPLb+Ms/xUdF1eulbt"
    "xe72X55njUXrqbnCdqF5UjQpWLn7dZ/SbjHi/qr5ZfxR8svaXFJne91XM9T1KvdTWHUk2l4LuXwWEdZq2bcnlHdwtKhRUXzOerW1"
    "1G0dYrWjb6E2+m1a9RwpxXJOUpNpRjFdZNvkku9vkjs1zQsrDTKuq6tdU7HTqPKdeour7oxS5zm+6K5/DmfHN/78r69CWl6XRnp+"
    "ip/3ltetuWukqzXXygvZXm+Z6qvW/Vh/1+dDttKE6zz3HIbm3lQsnOw21X454ca2pRWG/FUc84r8fq+7C5vo3rMmrxFJscajPdp0"
    "4wWEbtKrhnZtl7t1na2rR1LR7r1VTHBVpzXFSrw74VI/aj+ddU0zqEJGzSqYOiMozi4zWU+43jlbo9mdkvaFZ69Rlf6JV+j3tKCl"
    "faZVnxOK/Cj+HT8Jrmukku/65aXNhr9q61q+CtFffKMvrR//AF5n52aJqt7peo2+o6dd17S7t58dGtRlwzg/FP8ASujXJnp3sg7U"
    "rTc1e3tLipR0zc0eUFD2KN6+/wBWukZvvpvk/s+C+L49+nNObi35ea+PVe/mu/qenQrqp6s9mfY77T5Qb9k4i5tuHPI7NpWr2+sw"
    "dtXjG3vor6j5Kfu/YaOpW7hOUXHDR8lSqzhLRNYZ06GnhnWatPDMLgcjcU8M1nDn0PTjPKNIowwhlm7bU+aMdOHM5CxpZkiKs9jp"
    "gcxodt6ytBNcurfkfOvSL3c9D2FqtzRq8F3qj+5tlh84xkn6yS91NS+MkfUJy+g6NOceVWt97hjr5njz0nty/dff33GoVOKz0On9"
    "GST5OvLEq0vg+GH8Bm36ds/Tb9SkvVju/l93hfDJNapopt9dl+58juJLPJYS6I0qsjPWlzZqVGfo9xUyzxJyIk+ZD5jeRHA2YNiE"
    "+owwRkhsS5jSHGOTIocsgtyTGg8y3ESTyNEtgkykgwVjkaJGbYkikh4KSNEiXISiPhKiisFpEORPCVwlJDS8i0jNyEkNIaRSRokZ"
    "uQsBgtIfD5DSJbISHgrA0gwS5HF4EXgTRTR+m4IaE0W0Johohox4JZka5E4IwQ0Q0QzI0KSIaIaMeBYLwLBDRDRLRLRbEyHEhoxt"
    "CwZMEtEOJLRAd5WAaJwTgnAYKxyDHINJLRjaDBeBYE0SycCMgsC0kkiSLwPAtIiMCaMjQsBglkd40imhpA4kk4BIpLkPA1EROAwV"
    "geOZSiInA0h45lJFqIYEkUolJDSK0lJCUSuEaRcYlxiWkKEeZsU6eeb6CpwyzNjCwjaMe81jEG+WF0HCPMcYmejTbfQ2UWy8ZKoU"
    "m2uRzWm2bnJcjDYWzlJcjuu2dJlXqwShnJ1R0046pG8KWTldkbWr6pfUbejRlUqVJKMYpc2z1BoWi6Z2dba44wp1NTrQxOpj8y/F"
    "X52afYztK30HRPu5e00q9SDdLK+pDx97/QdY7UdxVK1WrOU2s8orPReB+ecS4hU4zeejU3/Ti9/e+nwPMu028ROgdpm56t1dVp1K"
    "znOTeW2fF9cvJVakm5ZOwbpvZVq825dWdMvpOTZ9/YW0bSgoxRz0bRRWTj7qpxPqaNR8zbrI1aiIqybOjs8GvIxyTM8kY5I4pIhx"
    "MEkS15GZxJaMWiGjE0JoyNCwTpM2jG0GDJwiaJaIIApoWBYIZLQmi2hYFgkjA8FYDBOCScCwXhj4WNRyS2SkPBcYMtQZSg2Q5GHh"
    "GombhSGo+BoqRm5mOMC1BGWFNvuM9K2lJ9GdELdvkjKVVI16cfI2aVJt8kcnZ6PXqJPg4Y+MuSN31OnWa++VPX1F3R6Ho0rNreR5"
    "1a7jnEd2aFnZ1Kr4Yxk8rHQ947E1L7s9k2j3s3xVa2k0lUf/AGlNKMvzwZ4anqsscFJRpR8InrD0TtXjq3ZTV02cs1NO1CrQxnpC"
    "rFVI/nlP5HzP6xow9EhUjzjJeD/nAWsqknJPbKNyVlK5vI0KS++VZqEfe31/pO0bjpwsdB+jUMRVSKo014U4Yz83j85WgaZP7pVK"
    "7jzpLgh+XLl+ZZ+ZrbjnO81P1FGLnCnilTwuuP2vLPkZ1u1rRintHf8APzqcMf6dByfOWy/PzuPn13bSUn7LbOC3hreibM0yN/r8"
    "5VLmtFytNOpSSrXHm/wKfjN+5JszdrnaXo2x41tK0lW+qbmS4ZRft0LF+NT8Op/2a6fa8H5c1vVNQ1fVK+p6peVr28uJcVWtWlxS"
    "k/2LuS5JdD6W0hUrxUpbR838Oi9/h1NbTh7b1VPA5TfO7tX3dqivNTqRhSp5jbWlHKo20X9mEf0yfOXezrzeRNiPVilFYjyPehFR"
    "WEUi0zGslItM1RlizLCRrxMsE2bQbLRs05tPqbttWlGSabTTTTTxh+JoQizaopR+sdtKTRaPQnZR2uK/VHRN43ThdRxG11eTxxPu"
    "jXfj4Vf434R6F03V3cpafrf3quuVO6a5S8FP+t0Z4BoXSpv2Uj6t2V9r1zocKOibh9dfaIvZpVI+1Xsl+J+HT8ab6fZx0fzfG/07"
    "TuF2tqt+n7x+3J93R+lQuVjRU5deh6m1Gxq29VwqR68010a8UaE6XfgnbuvRlptvV9fR1fRLiPHb16E+LEfGD8u+Lw105HYaFja3"
    "0PW6fcU7iHgniUfJo+EnKVB4qeP5yfuO/Rp3fLqcFRpZkuRzOk2rnWikuptUdFrcXOHCvFk3+p2+l0pULKUa93JYco840/j4+RhO"
    "s6vq092aQ9b1Ybs4ftR3LQ2zt3U9amoyp6TbOVOL6VK7woR+M3FfBngXULmtc16lxcVZVa9WcqlWb6znJ5k/i22fe/Sr3lGcLPZF"
    "rW46lKor3VGn9Wph+qpPzSk5tdzcTzxVnnJ+g/pqy9Es9cuc/ouXju/g0ede1Vq0R5Lb7mKpLqa8y5y5mKR6VSWTzJMlgHeBg2Zt"
    "hyGllgkZqcMtcgSyTkVODZtwt26MpYfJo2dPs5VqkUk3k+jaN2e6lfbN1DWIW1T1VvWoxclHliXFn5YXzOuNOEI6pvC5fN7I6aVC"
    "VTkfKZ0mn0IccHYNW06VtUlGUcYOGqU2mTUpODOWpFxeDBjyGkU4tMaWSUjnbEkVFDSLSNUjNsIoeOYJFI0ijNyBLmNIqKKSKSIc"
    "iOEpIpR5lJF4IciUgwWkPhKwQ5EJFKPiUkWkGDNyOHwLBeBNFtH6y0Y2iWjI0TghohoholoyNCaIaIaMWBNGRolohozaMbQmi2hY"
    "ZDRDRGOYmW0S0S0Q0QxYLaDBGCWiGhYLwGBaSWjG0GDJgGhYJwY8BgtoMCwS0RgeEVjmAtJLRGAxyLwGBaSWiMBgvAYHpIaMeB4K"
    "wNIMCwTgMFYBIekkWAwPDHgaQCSHFDSyNIpIMDRSQoouKLSLSHFGWESYozU0XFGkUXBJLJSWR4WEZIR5nQomyRVKHQ3rWjlrkYqE"
    "OaOX0+jxSXI3hE3pwyzktEs+OpHkfbux7bK1LWbWlOHsOWZv8Vc2fN9rWDnWguHvPTXYjpcLeNa5cUpKnhfFnz36n4g7a1koPc7a"
    "keyouR3Hd1aNrpCoUkoxxhJdyXRHm3tEup1K9TnyPRO/E3bePsnnXfVCTq1Hg+V/ScYp6meXRoao5PkWsOTqSOvXUebO16vbyU5c"
    "jr9zQll8j9Se8TSVLBwtWJrTj5HJ1qL58jWqUvI5ZxMJQOPlExyibs6fMxygc0onPKODUcfIlxNmUCHAxcTFo1nEXCbDgTwcyXEy"
    "ZgwLhRn4BcDI0mUjBwsODxNhU34MtUJS6JhobM2zU4eYnA3o2s33YB0Ix6y+RSoSZm5GkoMpU2+428QXRZ94m2+S5FdglzM3M11R"
    "feNQivMzcEmZKdvKXRM0jSzyRlKokay8lgpU22cnaaVcV5qNOnOTfclk5y22tXp01UvJQtqfjUeH8jpjZyftbHJUuoQ5s6pC3lLu"
    "N+y0m4uGlTpSl7kdgnU0HTV7PFeVF8ImhfbmuJwdO3ULeHcqax+c6FQpU95HK69ap7EfEyw0SjbRUr6vCkvwc5ZNTULC05WlBTkv"
    "tzOv3F7UqycpTbb728mvOs2+pM72ENoIFaTnvUeTlr3Vbiu/bqPHguSOPlXk31NV1H4kueTgqXkpd51QtowWEja9cz7R6KvaTpmy"
    "9z32m7guY2ul6vCmvpM/qUK9NvglLwi1KUW+7lnlk+HKRcZnn3dON3RlRqcmXGOh5R+k9e+0mhpVbVKerafTs+B1VdSuqape19rj"
    "zjCR5f7Y+2/Kr6FsG4nTotOFxrCTjUqro40E+cI/jv2n3YXN+e1UxFRwuFPKXcKdVy6s8mx4HRtpOVSWvpthfPnn6e4zlTjJppcg"
    "q1JOTbeW3kwy5jlzJXU9tvJ0QjgAwUotlRptjjBs2TIRcY5MsKLMmIQ6vL8jojQfNlJmOFPPcZowjH6zIdXlhYRDm2aaoQLTNh1M"
    "clyEqhr8Q1ITrNlo2Y1DPRqNc8mhGRkjMqNVotM+j9l/aRrOxr6TtVC+0yvLiutOryap1X+FFrnCp+MuvRpo9C7e7VuznXaMalPW"
    "vuFdvrb6knSaflVjmEl55XuPHEauO8yRrtd5599wy2vZa5ZjLqu/49z+vvOujeVKXss9oanvbaltTc7vfOjukvDUlVb90Ytt/I+d"
    "b77drSzs6lhseFStdSTi9TuKXBGl50qb5uXhKWEvBnnV1/DkRKq8HNQ4Ja03meZe58vD+ce46KvE6tSOnZL3G1f3dW5r1K9erUq1"
    "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"
    "a71LB2/Su2DVbeKjVufXx/HfP5nzcv03xG1eaE8nMrapS/tVNujOw652Z3CTlC2lJfirJ0nVez26g3m1qL3xZ3S07ZqdTCq1qtB+"
    "PBGov6H+c5Sn2rRqRzS1HSK34tWMqUvz8vznXRr8attpQz4/bBea+PWSfzPiN/se6hJ/eJfI4e62fdxeFQk/gegq/abe4co6Jp9y"
    "vGlLj/Rk4m97Xq9DPFtqzi/xqT/YetQ4vxV7din/APsjnqQl3x8z4LPZt/J8reb+A6ew9Wn9WyrPPhBn2K67cLynn1Wj6ZTf/c5O"
    "C1Ht13LJNUI2dH8i3ielTvOMVOVCK+Mv4OGaj3o6NQ7MNxXGPVaVdSz/ANmzkrXsa3PU51NP9RHxqzUSdT7Yt43DkpatWgn3U8R/"
    "QdU1ffOv33F6/Urupn8KtJ/0nbFcWl7ThHxf2OOpo6HeZdktCzjxapr+l2iXVOqmzUraL2d6S/7q12pezXWNCny+Z8sutYvKkm51"
    "ZNvxZx1xe1Z9ZM1VCv8A/LXb+CS+7OObXcj6rdbp2TYZWnaC68l0nXn/AEczhdR7Sr5RcLC3tbOPd6umsr5nzipWm/E1pzm/EOzo"
    "x5rV8W39TllHJ2TVd2atft/SL6vNeDny+RwNe+qTbzNmo5S7zHLmVK5kliOyMuzRlqV2+8wTqy8RNMXA/A5J1JyDSkTKbZDbMjpv"
    "wBUm+4xakw2RhJeTajbyfcy1Z1H9ljVGcuSDKNHD8AUWch9Dx9aUV72P1NCPWon7kWrWffsS5GgoN9xcaTfcbnHbw6RcvexO5S+r"
    "CK+BSoU17UiHJmKFtOX2WZY2uPrtR97Id1UfLifwMUqrb6lKVGPJZE1Jm0oUIdW5e4Uq8I/Ugl7zUc2LiB3OPZWA0dTYnXnJ85GN"
    "zb7zEMxlVlLmxqCRXExB1GTnJWBMCgwIonAYGMB5FgMDGMMkpFJCwNCYZABhjkSGSRpDwGBC1Ag7xoaQITkGB4GkUkVghyJSZaQ0"
    "ilEeDNyFgaKSGolJGbkJRKUSoxK4S1EzciOEpItRKUS1EhzISLjEpRKUfItRIcxRiWojjEyRiWombmRGJagWolRj5GiRlKZCiZIR"
    "LUS1AtIxlMlRKUSki0h4M3IiMS1HJUYlJYKSMnIhRK4S0hpDIcjFw5FwczMkPhAnWdawJoy45i4fI6cH77pMeBNGVoloTRLiYsCa"
    "MuCWuZOCHExNEtGVololozaMTQmjI0JxIcTNoxYE0ZXHvE4shoyaMeBNFtCwQ4kNGPAYMmPIeCGiGiEuQMvAmicENGNiSMjQsBgh"
    "onAsGTAsBglonA0h4HgWCWS0IvAYFghkYBorADwQTgCscsiaFgkloMFYY8CwIgaGNIeBiSKiMELAxlIkpe4pFGSJalgxZGmUmUmZ"
    "ozM0JmomWpFKRakb0KuDYp3DXecYp+ZSqFqZSqYOZp3bX2jPTvpL7RwSqspVn4lqqaKtg7HDUZL7Rf3UmvtHXFcPxG7h+I+2K9IZ"
    "2OOq1F9r84PV6mPrv5nW3cPxIdw/EXbIh3DOyrWq1N5hVlF+KeDLHdmrUuUNQuEvB1G1+c6lK4fiY5Vm+8iVaL5oxlcvqdvnvHUp"
    "f32dGt+XRi/6DFLdCl/fbC0l7ouP6GdRlVfiQ6rM+3UeSMJXEup2upr1jU+vpsV+TVaMEtT0yXW2rR900/6DrLqmN1WP0xo5pVWz"
    "sk7rSpfZrr5MwznpUukqy+COA9axOb8SXe+4ylPJzcnpvdUq/wAUxSen/h1f4qOI42J1H4kO9X+KMnL3HKSdhn61T5IxSdjnl6x/"
    "I41zfiS5vxId3/xRm2clKpaLpTm/iS69ulyofORx/E/EOIl3b7kjM3ncwS5UYL85Du5L6qivcjTcickO6mJo25XdR/bfwMcq85dZ"
    "P5mvzAzdeb5snBklVfiQ5vxJEZubYsIriYs57xYGTkWAQwQ8DQCwHxHgaRWBElJDUR4wVgBYGugYBLmMQ8APANMMBklDSGojwAZE"
    "kGCkh4DAskDwNoMeIYFqECWS0ilEWBajY02xrX11StbanKrWqzUKcI9ZSbwkveyL21qW1xUoVouFSnJxlF9U08NDo1JU3xRbTXeK"
    "pOU5ZfNmmI6feNzWDXwUkVwlKJmkZORKRaRXCUolJESkQkWkCRcUXgzchJFJFJDUS0jNyEkWojijJGPkUkZykSolKJaiUo+RppM3"
    "MhQKUDKolRgUkZuZEYGSMeRSiXGJaRm5kKJUYmRRKUSkZykTGJSWSlHJaRWDFyMeCootRKUSsGbkSolJFpD4RkORjSKSKSK4QM3I"
    "hRHw5LSDh5iYsnWcBgyKIYO3B/ROCMEtGXBLQsCwYWhNGbhJwLSZuJhkiWjO4kSiS0ZuJhwJozNEuJDRm4mLANGRoTRLiZuJiaJa"
    "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"
    "YFoUmQ3zCTIbAtDciWxZFIRQNkt8xNiySwP/2Q=="
)

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s %(message)s")
    logging.getLogger("telethon").setLevel(logging.WARNING)
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
    except (TelegramAPIError, TokenValidationError, errors.RPCError, sqlite3.Error, OSError, ValueError) as exc:
        LOG.error("Не удалось запустить acczHELP: %s", type(exc).__name__)
        raise SystemExit(1) from None
