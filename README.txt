Cloud Vision Web V4.4－Xvfb 套件名稱修正版

本版針對 Railway Log：
RuntimeError: 找不到 Xvfb

修正內容：
1. nixpacks.toml 將錯誤套件名稱 xvfb 改為 Nix 正式套件 xorg.xvfb。
2. xauth 改為 xorg.xauth。
3. 建置階段加入 command -v Xvfb 與 command -v xauth，若沒有真正安裝，Build 階段就會直接顯示原因。
4. app.py、V4.4 雙入口與所有功能均未更動。

GitHub 最外層必須只有一份：
app.py
requirements.txt
nixpacks.toml
README.txt
