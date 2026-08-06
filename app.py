from __future__ import annotations

import io
import json
import os
import secrets
import sqlite3
import time
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

from flask import Flask, Response, jsonify, redirect, render_template_string, request, send_file, session, url_for
from openpyxl import Workbook
from openpyxl.styles import Alignment, Font, PatternFill

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.getenv("DATA_DIR", BASE_DIR / "data"))
DATA_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = DATA_DIR / "cloudvision.db"

app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", secrets.token_hex(24))
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD", "123456")


def db_connect() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db() -> None:
    with db_connect() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS test_sessions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                session_code TEXT NOT NULL UNIQUE,
                created_at TEXT NOT NULL,
                started_at TEXT NOT NULL,
                completed_at TEXT NOT NULL,
                duration_seconds INTEGER NOT NULL DEFAULT 0,
                subject_name TEXT NOT NULL DEFAULT '',
                subject_code TEXT NOT NULL DEFAULT '',
                right_eye TEXT NOT NULL DEFAULT '',
                left_eye TEXT NOT NULL DEFAULT '',
                both_eyes TEXT NOT NULL DEFAULT '',
                calibration_value REAL NOT NULL DEFAULT 1.0,
                device_type TEXT NOT NULL DEFAULT '',
                notes TEXT NOT NULL DEFAULT ''
            )
            """
        )
        conn.execute("CREATE INDEX IF NOT EXISTS idx_sessions_created ON test_sessions(created_at)")
        conn.commit()


init_db()

BASE_CSS = r"""
:root{--blue:#214f9a;--blue2:#376cc0;--ink:#202a37;--muted:#657084;--line:#dce3ed;--bg:#f5f8fc;--card:#fff;--ok:#177245;--danger:#a72f2f}
*{box-sizing:border-box}body{margin:0;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI","Noto Sans TC",Arial,sans-serif;background:var(--bg);color:var(--ink)}
a{color:var(--blue)}.wrap{width:min(1050px,calc(100% - 28px));margin:0 auto;padding:28px 0 50px}.top{text-align:center;padding:20px 0}.brand{color:var(--blue);font-weight:800;letter-spacing:.08em}.top h1{font-size:clamp(32px,6vw,52px);margin:12px 0}.sub{color:var(--muted);line-height:1.7}.card{background:var(--card);border:1px solid var(--line);border-radius:22px;padding:24px;margin:18px 0;box-shadow:0 12px 30px rgba(35,61,99,.07)}
.grid{display:grid;gap:16px}.grid.two{grid-template-columns:repeat(2,minmax(0,1fr))}.grid.four{grid-template-columns:repeat(4,minmax(0,1fr))}.feature{padding:22px;border:1px solid var(--line);border-radius:18px;background:#fff}.feature h3{color:var(--blue);font-size:24px;margin:0 0 8px}.btn{display:inline-flex;align-items:center;justify-content:center;border:0;border-radius:14px;padding:14px 22px;background:var(--blue);color:#fff;text-decoration:none;font-size:17px;font-weight:800;cursor:pointer}.btn:hover{background:var(--blue2)}.btn.secondary{background:#eef3fb;color:var(--blue)}.btn.danger{background:var(--danger)}.actions{display:flex;gap:12px;flex-wrap:wrap;align-items:center}.field{display:grid;gap:7px;margin:12px 0}.field label{font-weight:750}.field input,.field textarea{width:100%;border:1px solid #cfd8e5;border-radius:12px;padding:13px 14px;font-size:17px}.notice{padding:14px 16px;border-radius:12px;background:#eef7f2;color:var(--ok);font-weight:700}.small{font-size:14px;color:var(--muted)}
.cal-line-wrap{overflow:auto;padding:28px 10px}.cal-line{height:7px;background:#111;border-radius:4px;margin:auto}.eye-card{text-align:center}.eye-title{font-size:28px;font-weight:850;color:var(--blue)}.cover-note{font-size:18px;padding:12px;background:#fff5cf;border-radius:12px;margin:14px 0}.optotype-stage{min-height:300px;display:grid;place-items:center;background:#fff;border:1px solid var(--line);border-radius:20px;margin:18px 0}.landolt{position:relative;border-style:solid;border-color:#111;border-radius:50%;display:block}.landolt::after{content:"";position:absolute;background:#fff}.landolt.gap-right::after{right:-4px;top:35%;width:42%;height:30%}.landolt.gap-left::after{left:-4px;top:35%;width:42%;height:30%}.landolt.gap-up::after{top:-4px;left:35%;width:30%;height:42%}.landolt.gap-down::after{bottom:-4px;left:35%;width:30%;height:42%}.dir-grid{display:grid;grid-template-columns:repeat(4,1fr);gap:12px}.dir{font-size:30px;padding:18px 8px;border:1px solid #bfd0e8;border-radius:16px;background:#f7faff;color:var(--blue);cursor:pointer}.progress{height:12px;background:#e8eef6;border-radius:999px;overflow:hidden}.progress>div{height:100%;background:var(--blue);width:0}.result-number{font-size:54px;font-weight:900;color:var(--blue);margin:8px 0}.table-scroll{overflow:auto}table{border-collapse:collapse;width:100%;min-width:850px}th,td{padding:11px;border-bottom:1px solid var(--line);text-align:left}th{background:#eef3fb}.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:14px}.stat{background:#eef3fb;border-radius:16px;padding:18px}.stat b{display:block;font-size:30px;color:var(--blue)}
@media(max-width:760px){.grid.two,.grid.four,.stats{grid-template-columns:1fr}.dir-grid{grid-template-columns:repeat(2,1fr)}.card{padding:18px}.wrap{width:min(100% - 18px,1050px)}}
"""

HOME_HTML = r"""
<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Cloud Vision 視覺功能自我篩檢</title><style>{{ css }}</style></head><body>
<main class="wrap"><header class="top"><div class="brand">Cloud Vision</div><h1>視覺功能自我篩檢</h1><p class="sub">手機、iPad、電腦皆可使用。結果僅供自我了解，不能取代專業眼科或驗光檢查。</p></header>
<section class="card"><h2>開始前</h2><p>請戴平常使用的眼鏡、保持螢幕亮度穩定，並先完成 5 公分校正。</p><div class="actions"><a class="btn secondary" href="{{ url_for('calibration') }}">先做 5 公分校正</a><a class="btn" href="{{ url_for('test_info') }}">開始三眼視力測驗</a></div></section>
<section class="grid two"><div class="feature"><h3>1 公尺</h3><p>依序測量右眼、左眼、雙眼。</p></div><div class="feature"><h3>30 公分</h3><p>近距閱讀評估，下一階段加入。</p></div><div class="feature"><h3>散光鐘</h3><p>左右眼分開觀察，下一階段加入。</p></div><div class="feature"><h3>阿姆斯勒方格</h3><p>黃斑部線條觀察，下一階段加入。</p></div></section>
<p style="text-align:center"><a href="{{ url_for('admin_login') }}">今日資料管理</a></p></main></body></html>
"""

CAL_HTML = r"""
<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>5 公分校正</title><style>{{ css }}</style></head><body><main class="wrap">
<header class="top"><div class="brand">Cloud Vision</div><h1>5 公分螢幕校正</h1><p class="sub">請用實體尺量下面黑線，輸入你量到的長度。</p></header>
<section class="card"><div class="cal-line-wrap"><div id="line" class="cal-line"></div></div><div class="field"><label for="measured">實際量到幾公分？</label><input id="measured" type="number" min="1" max="10" step="0.1" value="5.0" inputmode="decimal"></div><p id="status" class="small"></p><div class="actions"><button class="btn" onclick="saveCal()">儲存校正</button><a class="btn secondary" href="{{ url_for('general_home') }}">回首頁</a></div></section></main>
<script>
const nominalPxPerMm=96/25.4; const line=document.getElementById('line');
function draw(){const factor=parseFloat(localStorage.getItem('cv_cal_factor')||'1');line.style.width=(50*nominalPxPerMm*factor)+'px';document.getElementById('status').textContent='目前校正倍率：'+factor.toFixed(3)}draw();
function saveCal(){const m=parseFloat(document.getElementById('measured').value);if(!m||m<=0){alert('請輸入實際量到的公分數');return}const old=parseFloat(localStorage.getItem('cv_cal_factor')||'1');const factor=old*(5/m);localStorage.setItem('cv_cal_factor',factor.toString());draw();alert('校正完成，請再量一次；接近 5 公分即可開始測驗。')}
</script></body></html>
"""

INFO_HTML = r"""
<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>開始三眼視力測驗</title><style>{{ css }}</style></head><body><main class="wrap"><header class="top"><div class="brand">Cloud Vision</div><h1>三眼視力測驗</h1><p class="sub">測試距離為 1 公尺，流程為右眼 → 左眼 → 雙眼。</p></header>
<section class="card"><form id="info"><div class="grid two"><div class="field"><label>姓名（可不填）</label><input name="subject_name" maxlength="30"></div><div class="field"><label>受測者代碼（可不填）</label><input name="subject_code" maxlength="30" placeholder="例如 A001"></div></div><div class="field"><label>備註（可不填）</label><textarea name="notes" rows="3"></textarea></div><div class="notice">請先確認已完成 5 公分校正，並讓眼睛距離螢幕約 1 公尺。</div><br><button class="btn" type="submit">開始測驗</button></form></section></main>
<script>document.getElementById('info').addEventListener('submit',e=>{e.preventDefault();const d=Object.fromEntries(new FormData(e.target));sessionStorage.setItem('cv_subject',JSON.stringify(d));sessionStorage.setItem('cv_started_at',new Date().toISOString());location.href='{{ url_for("acuity_test") }}';});</script></body></html>
"""

TEST_HTML = r"""
<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>三眼視力測驗</title><style>{{ css }}</style></head><body><main class="wrap"><header class="top"><div class="brand">Cloud Vision</div><h1>1 公尺三眼視力測驗</h1></header>
<section class="card eye-card"><div class="progress"><div id="bar"></div></div><p id="phase" class="eye-title"></p><div id="cover" class="cover-note"></div><p id="levelText" class="small"></p><div class="optotype-stage"><span id="optotype" class="landolt"></span></div><p>請選擇缺口方向</p><div class="dir-grid"><button class="dir" data-dir="up">↑</button><button class="dir" data-dir="down">↓</button><button class="dir" data-dir="left">←</button><button class="dir" data-dir="right">→</button></div></section></main>
<script>
const levels=[0.2,0.3,0.4,0.5,0.6,0.8,1.0,1.2]; const eyes=[{key:'right_eye',name:'右眼',cover:'請遮住左眼，只用右眼看。'},{key:'left_eye',name:'左眼',cover:'請遮住右眼，只用左眼看。'},{key:'both_eyes',name:'雙眼',cover:'請張開雙眼一起看。'}];
const dirs=['up','down','left','right']; let eyeIndex=0,levelIndex=0,trial=0,correct=0,current='',results={}; const trialsPerLevel=5;
function shuffledDir(){return dirs[Math.floor(Math.random()*dirs.length)]}
function physicalSizeMm(v){return 1000*Math.tan((5/v)*Math.PI/(180*60))}
function render(){const e=eyes[eyeIndex],v=levels[levelIndex];document.getElementById('phase').textContent=e.name+'視力';document.getElementById('cover').textContent=e.cover;document.getElementById('levelText').textContent='目前等級 '+v.toFixed(1)+'　題目 '+(trial+1)+' / '+trialsPerLevel;const total=(eyeIndex*levels.length*trialsPerLevel)+(levelIndex*trialsPerLevel)+trial;document.getElementById('bar').style.width=Math.min(100,total/(eyes.length*levels.length*trialsPerLevel)*100)+'%';current=shuffledDir();const factor=parseFloat(localStorage.getItem('cv_cal_factor')||'1');const pxPerMm=(96/25.4)*factor;const size=Math.max(12,physicalSizeMm(v)*pxPerMm);const stroke=size/5;const o=document.getElementById('optotype');o.className='landolt gap-'+current;o.style.width=size+'px';o.style.height=size+'px';o.style.borderWidth=stroke+'px'}
function answer(dir){if(dir===current)correct++;trial++;if(trial<trialsPerLevel){render();return}const passed=correct>=3;if(passed){results[eyes[eyeIndex].key]=levels[levelIndex].toFixed(1);levelIndex++;trial=0;correct=0;if(levelIndex<levels.length){render();return}}finishEye()}
function finishEye(){if(!results[eyes[eyeIndex].key])results[eyes[eyeIndex].key]=levelIndex===0?'<0.2':levels[Math.max(0,levelIndex-1)].toFixed(1);eyeIndex++;levelIndex=0;trial=0;correct=0;if(eyeIndex<eyes.length){alert('接下來測量'+eyes[eyeIndex].name+'。');render();return}saveAll()}
async function saveAll(){const subject=JSON.parse(sessionStorage.getItem('cv_subject')||'{}');const started=sessionStorage.getItem('cv_started_at')||new Date().toISOString();const payload={...subject,...results,started_at:started,completed_at:new Date().toISOString(),calibration_value:parseFloat(localStorage.getItem('cv_cal_factor')||'1'),device_type:navigator.userAgent};const r=await fetch('{{ url_for("api_save") }}',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});const out=await r.json();if(!r.ok){alert(out.error||'儲存失敗');return}sessionStorage.setItem('cv_result',JSON.stringify({...results,session_code:out.session_code}));location.href='{{ url_for("result") }}'}
document.querySelectorAll('.dir').forEach(b=>b.addEventListener('click',()=>answer(b.dataset.dir)));render();
</script></body></html>
"""

RESULT_HTML = r"""
<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>測驗結果</title><style>{{ css }}</style></head><body><main class="wrap"><header class="top"><div class="brand">Cloud Vision</div><h1>個人測驗結果</h1><p class="sub">此結果僅供自我了解，不能取代專業檢查。</p></header><section class="grid four"><div class="card eye-card"><h2>右眼</h2><div id="r" class="result-number">—</div></div><div class="card eye-card"><h2>左眼</h2><div id="l" class="result-number">—</div></div><div class="card eye-card"><h2>雙眼</h2><div id="b" class="result-number">—</div></div><div class="card eye-card"><h2>紀錄代碼</h2><div id="c" style="font-size:21px;font-weight:800">—</div></div></section><section class="card"><p>若左右眼差異明顯、看不清楚，或有視物扭曲、眼痛、突然視力下降等情況，請安排專業眼科或驗光檢查。</p><div class="actions"><a class="btn" href="{{ url_for('test_info') }}">重新測驗</a><a class="btn secondary" href="{{ url_for('general_home') }}">回首頁</a></div></section></main><script>const d=JSON.parse(sessionStorage.getItem('cv_result')||'{}');r.textContent=d.right_eye||'—';l.textContent=d.left_eye||'—';b.textContent=d.both_eyes||'—';c.textContent=d.session_code||'—';</script></body></html>
"""

LOGIN_HTML = r"""
<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>管理者登入</title><style>{{ css }}</style></head><body><main class="wrap"><header class="top"><div class="brand">Cloud Vision</div><h1>今日資料管理</h1></header><section class="card" style="max-width:520px;margin:auto"><form method="post"><div class="field"><label>6 碼管理密碼</label><input name="password" type="password" inputmode="numeric" maxlength="20" required></div>{% if error %}<p style="color:#a72f2f;font-weight:700">{{ error }}</p>{% endif %}<button class="btn">登入</button></form></section></main></body></html>
"""

ADMIN_HTML = r"""
<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>今日資料管理</title><style>{{ css }}</style></head><body><main class="wrap"><header class="top"><div class="brand">Cloud Vision</div><h1>今日資料管理</h1><div class="actions" style="justify-content:center"><a class="btn" href="{{ url_for('export_excel') }}">下載全部 Excel</a><a class="btn secondary" href="{{ url_for('general_home') }}">回首頁</a><a class="btn secondary" href="{{ url_for('admin_logout') }}">登出</a></div></header><section class="stats"><div class="stat"><span>今日完成</span><b>{{ stats.today_count }}</b></div><div class="stat"><span>全部紀錄</span><b>{{ stats.total_count }}</b></div><div class="stat"><span>今日平均秒數</span><b>{{ stats.avg_duration }}</b></div><div class="stat"><span>最近完成</span><b style="font-size:17px">{{ stats.latest or '—' }}</b></div></section><section class="card"><div class="table-scroll"><table><thead><tr><th>時間</th><th>姓名/代碼</th><th>右眼</th><th>左眼</th><th>雙眼</th><th>秒數</th><th>裝置</th></tr></thead><tbody>{% for r in rows %}<tr><td>{{ r.completed_at }}</td><td>{{ r.subject_name }} {{ r.subject_code }}</td><td>{{ r.right_eye }}</td><td>{{ r.left_eye }}</td><td>{{ r.both_eyes }}</td><td>{{ r.duration_seconds }}</td><td>{{ r.device_type[:45] }}</td></tr>{% else %}<tr><td colspan="7">目前尚無紀錄。</td></tr>{% endfor %}</tbody></table></div></section></main></body></html>
"""


def render(page: str, **ctx: Any) -> str:
    return render_template_string(page, css=BASE_CSS, **ctx)


@app.get('/health')
def health() -> Response:
    return Response('ok', status=200, mimetype='text/plain')


@app.get('/general')
def general_home() -> str:
    return render(HOME_HTML)


@app.get('/calibration')
def calibration() -> str:
    return render(CAL_HTML)


@app.get('/test-info')
def test_info() -> str:
    return render(INFO_HTML)


@app.get('/acuity-test')
def acuity_test() -> str:
    return render(TEST_HTML)


@app.get('/result')
def result() -> str:
    return render(RESULT_HTML)


@app.post('/api/save')
def api_save() -> Response:
    data = request.get_json(silent=True) or {}
    required = ('right_eye', 'left_eye', 'both_eyes')
    if not all(str(data.get(k, '')).strip() for k in required):
        return jsonify({'error': '三眼視力資料不完整'}), 400
    try:
        started = datetime.fromisoformat(str(data.get('started_at')).replace('Z', '+00:00'))
        completed = datetime.fromisoformat(str(data.get('completed_at')).replace('Z', '+00:00'))
        duration = max(0, int((completed - started).total_seconds()))
    except Exception:
        completed = datetime.now().astimezone()
        started = completed
        duration = 0
    code = datetime.now().strftime('%Y%m%d%H%M%S') + secrets.token_hex(2).upper()
    with db_connect() as conn:
        conn.execute(
            """INSERT INTO test_sessions
            (session_code,created_at,started_at,completed_at,duration_seconds,subject_name,subject_code,right_eye,left_eye,both_eyes,calibration_value,device_type,notes)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (code, datetime.now().astimezone().isoformat(timespec='seconds'), str(data.get('started_at','')), str(data.get('completed_at','')), duration,
             str(data.get('subject_name','')).strip(), str(data.get('subject_code','')).strip(), str(data.get('right_eye','')).strip(), str(data.get('left_eye','')).strip(), str(data.get('both_eyes','')).strip(),
             float(data.get('calibration_value') or 1.0), str(data.get('device_type',''))[:500], str(data.get('notes','')).strip())
        )
        conn.commit()
    return jsonify({'ok': True, 'session_code': code})


def admin_ok() -> bool:
    return bool(session.get('admin_ok'))



# ===== 雙入口首頁與專業人員區 =====
@app.get('/')
def home() -> str:
    body = r"""
    <header class="top"><div class="brand">Cloud Vision</div><h1>請選擇使用入口</h1>
    <p class="sub">一般使用者與專業人員使用不同入口；一般版保留原本已成功的雲端測驗流程。</p></header>
    <section class="grid two">
      <article class="card"><h2>一般使用者</h2><p>進行 5 公分校正、右眼、左眼與雙眼視力測驗，並保留使用時間與結果紀錄。</p>
      <a class="btn" href="{{ url_for('general_home') }}">進入一般使用者</a></article>
      <article class="card"><h2>專業人員</h2><p>完成專業身分登記後，進入專業教學與計算工具區。</p>
      <a class="btn" href="{{ url_for('professional') }}">進入專業人員</a></article>
    </section>
    """
    return render(body)


def ensure_professional_table() -> None:
    with db_connect() as conn:
        conn.execute("""
        CREATE TABLE IF NOT EXISTS professional_users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            created_at TEXT NOT NULL,
            last_login_at TEXT NOT NULL,
            login_count INTEGER NOT NULL DEFAULT 1,
            name TEXT NOT NULL,
            role TEXT NOT NULL,
            organization TEXT NOT NULL DEFAULT '',
            city TEXT NOT NULL DEFAULT '',
            responsibility INTEGER NOT NULL DEFAULT 1,
            privacy_consent INTEGER NOT NULL DEFAULT 1
        )
        """)
        conn.commit()


ensure_professional_table()


@app.route('/professional', methods=['GET', 'POST'])
def professional() -> str:
    professional_id = session.get('professional_id')
    if request.method == 'POST':
        name = request.form.get('name', '').strip()[:80]
        role = request.form.get('role', '').strip()[:80]
        organization = request.form.get('organization', '').strip()[:120]
        city = request.form.get('city', '').strip()[:40]
        if not name or not role or request.form.get('responsibility') != 'yes' or request.form.get('privacy') != 'yes':
            return render(PROFESSIONAL_REGISTER_HTML, error='請完整填寫姓名、身分類別，並勾選兩項同意聲明。')
        now = datetime.now().isoformat(timespec='seconds')
        with db_connect() as conn:
            cur = conn.execute("""INSERT INTO professional_users
                (created_at,last_login_at,login_count,name,role,organization,city,responsibility,privacy_consent)
                VALUES (?,?,?,?,?,?,?,1,1)""", (now,now,1,name,role,organization,city))
            conn.commit()
            professional_id = cur.lastrowid
        session['professional_id'] = professional_id
        return redirect(url_for('professional'))
    if not professional_id:
        return render(PROFESSIONAL_REGISTER_HTML, error='')
    with db_connect() as conn:
        user = conn.execute('SELECT * FROM professional_users WHERE id=?', (professional_id,)).fetchone()
    if not user:
        session.pop('professional_id', None)
        return redirect(url_for('professional'))
    return render(PROFESSIONAL_CENTER_HTML, professional_name=user['name'], professional_role=user['role'])


@app.get('/professional/logout')
def professional_logout():
    session.pop('professional_id', None)
    return redirect(url_for('home'))


PROFESSIONAL_REGISTER_HTML = r"""
<header class="top"><div class="brand">Cloud Vision｜專業人員</div><h1>專業使用者登記</h1>
<p class="sub">第一次進入完成登記後即可使用。</p></header>
<section class="card"><div class="notice" {% if not error %}style="display:none"{% endif %}>{{ error }}</div>
<form method="post">
<div class="field"><label>姓名</label><input name="name" required></div>
<div class="field"><label>身分類別</label><input name="role" placeholder="例如：驗光師、教師、學生、研究人員" required></div>
<div class="field"><label>服務單位或學校</label><input name="organization"></div>
<div class="field"><label>縣市</label><input name="city"></div>
<p><label><input type="checkbox" name="responsibility" value="yes" required> 我了解本平台僅供教學、研究及專業輔助，不取代醫療診斷或完整驗光。</label></p>
<p><label><input type="checkbox" name="privacy" value="yes" required> 我同意基本登記資料用於資格登記、統計與系統管理。</label></p>
<button class="btn" type="submit">完成登記並進入</button> <a class="btn secondary" href="{{ url_for('home') }}">返回雙入口</a>
</form></section>
"""

PROFESSIONAL_CENTER_HTML = r"""
<header class="top"><div class="brand">Cloud Vision｜專業人員</div><h1>專業教學中心</h1>
<p class="sub">{{ professional_name }}（{{ professional_role }}），歡迎使用。</p></header>
<section class="grid two">
<div class="card"><h2>一般測驗流程示範</h2><p>可直接使用已完成的校正及三眼視力測驗流程。</p><a class="btn" href="{{ url_for('calibration') }}">進入 5 公分校正</a></div>
<div class="card"><h2>專業幾何與教學工具</h2><p>此入口保留給專業視力幾何、字高與距離換算等後續工具。</p><a class="btn secondary" href="{{ url_for('general_home') }}">查看目前測驗工具</a></div>
</section><p style="text-align:center"><a href="{{ url_for('professional_logout') }}">登出專業入口</a></p>
"""

@app.route('/admin/login', methods=['GET','POST'])
def admin_login() -> str | Response:
    error = ''
    if request.method == 'POST':
        if request.form.get('password','') == ADMIN_PASSWORD:
            session['admin_ok'] = True
            return redirect(url_for('admin'))
        error = '密碼錯誤。'
    return render(LOGIN_HTML, error=error)


@app.get('/admin/logout')
def admin_logout() -> Response:
    session.clear()
    return redirect(url_for('general_home'))


@app.get('/admin')
def admin() -> str | Response:
    if not admin_ok():
        return redirect(url_for('admin_login'))
    today = datetime.now().astimezone().date().isoformat()
    with db_connect() as conn:
        rows = conn.execute('SELECT * FROM test_sessions ORDER BY id DESC LIMIT 100').fetchall()
        total_count = conn.execute('SELECT COUNT(*) FROM test_sessions').fetchone()[0]
        today_row = conn.execute("SELECT COUNT(*), COALESCE(AVG(duration_seconds),0) FROM test_sessions WHERE substr(created_at,1,10)=?", (today,)).fetchone()
    stats = {'today_count': today_row[0], 'total_count': total_count, 'avg_duration': int(today_row[1] or 0), 'latest': rows[0]['completed_at'] if rows else ''}
    return render(ADMIN_HTML, rows=rows, stats=stats)


@app.get('/export.xlsx')
def export_excel() -> Response:
    if not admin_ok():
        return redirect(url_for('admin_login'))
    with db_connect() as conn:
        rows = conn.execute('SELECT * FROM test_sessions ORDER BY id ASC').fetchall()
    wb = Workbook(); ws = wb.active; ws.title = '三眼視力紀錄'
    headers = ['編號','紀錄代碼','建立時間','開始時間','完成時間','測驗秒數','姓名','受測者代碼','右眼','左眼','雙眼','校正倍率','裝置','備註']
    ws.append(headers)
    fill = PatternFill('solid', fgColor='DDEBF7')
    for c in ws[1]: c.font=Font(bold=True); c.fill=fill; c.alignment=Alignment(horizontal='center')
    for r in rows:
        ws.append([r['id'],r['session_code'],r['created_at'],r['started_at'],r['completed_at'],r['duration_seconds'],r['subject_name'],r['subject_code'],r['right_eye'],r['left_eye'],r['both_eyes'],r['calibration_value'],r['device_type'],r['notes']])
    for col,width in {'A':8,'B':22,'C':24,'D':24,'E':24,'F':12,'G':15,'H':18,'I':10,'J':10,'K':10,'L':12,'M':45,'N':30}.items(): ws.column_dimensions[col].width=width
    ws.freeze_panes='A2'; out=io.BytesIO(); wb.save(out); out.seek(0)
    return send_file(out, as_attachment=True, download_name=f'CloudVision_三眼視力_{datetime.now():%Y%m%d_%H%M}.xlsx', mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet')


if __name__ == '__main__':
    app.run(host='0.0.0.0', port=int(os.getenv('PORT','8080')), debug=False)
