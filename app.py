from __future__ import annotations

import io
import os
import sqlite3
from datetime import datetime
from pathlib import Path
from typing import Any

from flask import Flask, Response, flash, redirect, render_template, request, send_file, url_for
from openpyxl import Workbook
from openpyxl.styles import Alignment, Font, PatternFill

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.getenv("DATA_DIR", BASE_DIR / "data"))
DATA_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = DATA_DIR / "cloudvision.db"

app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", "cloudvision-v42-change-me")


def db_connect() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db() -> None:
    with db_connect() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS acuity_records (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                created_at TEXT NOT NULL,
                examiner TEXT NOT NULL DEFAULT '',
                subject_code TEXT NOT NULL DEFAULT '',
                right_eye TEXT NOT NULL DEFAULT '',
                left_eye TEXT NOT NULL DEFAULT '',
                both_eyes TEXT NOT NULL DEFAULT '',
                notes TEXT NOT NULL DEFAULT ''
            )
            """
        )
        conn.commit()


init_db()


@app.get("/health")
def health() -> Response:
    return Response("ok", status=200, mimetype="text/plain")


@app.route("/", methods=["GET", "POST"])
def index() -> str | Response:
    if request.method == "POST":
        subject_code = request.form.get("subject_code", "").strip()
        examiner = request.form.get("examiner", "").strip()
        right_eye = request.form.get("right_eye", "").strip()
        left_eye = request.form.get("left_eye", "").strip()
        both_eyes = request.form.get("both_eyes", "").strip()
        notes = request.form.get("notes", "").strip()

        if not any((right_eye, left_eye, both_eyes)):
            flash("請至少填寫右眼、左眼或雙眼其中一項結果。", "error")
            return redirect(url_for("index"))

        with db_connect() as conn:
            conn.execute(
                """
                INSERT INTO acuity_records
                (created_at, examiner, subject_code, right_eye, left_eye, both_eyes, notes)
                VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    datetime.now().astimezone().isoformat(timespec="seconds"),
                    examiner,
                    subject_code,
                    right_eye,
                    left_eye,
                    both_eyes,
                    notes,
                ),
            )
            conn.commit()

        flash("三眼視力資料已儲存。", "success")
        return redirect(url_for("index"))

    with db_connect() as conn:
        records = conn.execute(
            "SELECT * FROM acuity_records ORDER BY id DESC LIMIT 20"
        ).fetchall()
    return render_template("index.html", records=records)


@app.get("/export.xlsx")
def export_excel() -> Response:
    with db_connect() as conn:
        rows = conn.execute(
            "SELECT * FROM acuity_records ORDER BY id ASC"
        ).fetchall()

    wb = Workbook()
    ws = wb.active
    ws.title = "三眼視力紀錄"
    headers = ["編號", "建立時間", "檢查人員", "受測者代碼", "右眼", "左眼", "雙眼", "備註"]
    ws.append(headers)

    header_fill = PatternFill("solid", fgColor="DDEBF7")
    for cell in ws[1]:
        cell.font = Font(bold=True)
        cell.fill = header_fill
        cell.alignment = Alignment(horizontal="center")

    for row in rows:
        ws.append([
            row["id"], row["created_at"], row["examiner"], row["subject_code"],
            row["right_eye"], row["left_eye"], row["both_eyes"], row["notes"]
        ])

    widths = {"A": 8, "B": 28, "C": 16, "D": 18, "E": 12, "F": 12, "G": 12, "H": 32}
    for column, width in widths.items():
        ws.column_dimensions[column].width = width
    ws.freeze_panes = "A2"

    output = io.BytesIO()
    wb.save(output)
    output.seek(0)
    filename = f"CloudVision_三眼視力_{datetime.now():%Y%m%d_%H%M}.xlsx"
    return send_file(
        output,
        as_attachment=True,
        download_name=filename,
        mimetype="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
    )


@app.post("/delete/<int:record_id>")
def delete_record(record_id: int) -> Response:
    with db_connect() as conn:
        conn.execute("DELETE FROM acuity_records WHERE id = ?", (record_id,))
        conn.commit()
    flash("紀錄已刪除。", "success")
    return redirect(url_for("index"))


if __name__ == "__main__":
    port = int(os.getenv("PORT", "8080"))
    app.run(host="0.0.0.0", port=port, debug=False)
