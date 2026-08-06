Cloud Vision Web V4.4 Xvfb 最終修正版

本次針對 Railway Log：
_tkinter.TclError: no display name and no $DISPLAY environment variable

修正方式：
1. Railway 建置時安裝 xvfb。
2. 整個 gunicorn 由 xvfb-run 啟動，讓主程序與背景 Tkinter 程序都繼承 DISPLAY。
3. V4.4 的首頁、雙入口、測驗與資料紀錄內容均未更改。

請將四個檔案放在 GitHub 專案最外層，並覆蓋同名舊檔。
