Cloud Vision Web V4.4 內建 Xvfb 修正版

修正內容：
1. Gunicorn 正常監聽 Railway 的 PORT。
2. 背景 V4.4 程序自行啟動 Xvfb :99。
3. 自動設定 DISPLAY=:99 後才建立 Tkinter。
4. 不再依賴 Railway 是否採用 xvfb-run 啟動命令。

GitHub 最外層只保留一份：
app.py
requirements.txt
nixpacks.toml
README.txt
