# CloudVision Web V1.0

可部署至 Render 的 Cloud Vision 公開自我篩檢網站。

## 本機執行

```bash
pip install -r requirements.txt
python app.py
```

打開 `http://127.0.0.1:5000/cloud`。

## Render

Build command: `pip install -r requirements.txt`  
Start command: `gunicorn app:app`
