# YouTube API

API بسيط بيستخرج روابط تحميل مباشرة لفيديوهات يوتيوب باستخدام yt-dlp.

## Endpoints

- `GET /` — فحص إن السيرفر شغال
- `GET /info?url=<رابط الفيديو>` — يرجع كل الصيغ والجودات المتاحة
- `GET /best?url=<رابط الفيديو>` — يرجع أفضل جودة بسرعة (رابط واحد)

## تشغيل محلي

```bash
pip install -r requirements.txt
uvicorn main:app --reload
```

هيشتغل على: http://localhost:8000

## رفعه على Render

1. ارفع المشروع ده على GitHub (repo جديد)
2. روح على render.com وسجل دخول بحساب GitHub
3. New + → Web Service → اختار الـ repo
4. Render هيكتشف الإعدادات تلقائي من render.yaml
5. اضغط Create Web Service

بعد الـ deploy هتاخد رابط زي:
`https://youtube-api-xxxx.onrender.com`
