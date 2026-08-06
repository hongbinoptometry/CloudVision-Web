Cloud Vision Web V4.4 成功雲端入口整合版

上傳到 Railway 的最外層檔案：
1. app.py
2. requirements.txt
3. nixpacks.toml

本版以 V4.4 為主程式，保留一般使用者／專業人員雙入口、登入與使用時間紀錄。
新增成功版的 Railway Gunicorn 入口，內部以 8765 埠啟動原本 Cloud Vision 網頁伺服器。
Railway 對外啟動命令已寫在 nixpacks.toml。
