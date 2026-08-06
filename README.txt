CloudVision Web V4.4 雲端啟動修正版

本次修正：
1. Railway 即使仍以 python app.py 啟動，也會自動切換成 Gunicorn Web 模式。
2. 不會再於 Railway 主程序直接執行 tk.Tk()，避免：
   _tkinter.TclError: no display name and no $DISPLAY environment variable
3. 只有內部 CLOUDVISION_BACKEND 程序才會透過 xvfb-run 執行 Tkinter。
4. V4.4 原本的一般使用者／專業人員雙入口及測驗、紀錄功能均保留。

上傳方式：
- GitHub 最外層只保留一份 app.py
- 只保留一份 requirements.txt
- 只保留一份 nixpacks.toml
- 舊的 app(1).py、app (6).py、nixpacks (1).toml 等重複檔請不要當成啟動檔

Railway 正常啟動命令：
gunicorn app:app --bind 0.0.0.0:$PORT --workers 1 --threads 4 --timeout 180
