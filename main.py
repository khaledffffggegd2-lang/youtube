from fastapi import FastAPI, HTTPException, Query
from fastapi.middleware.cors import CORSMiddleware
import yt_dlp

app = FastAPI(title="YouTube Downloader API")

# يسمح لأي تطبيق (زي تطبيق الأندرويد بتاعك) يكلم الـ API
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.get("/")
def home():
    return {"status": "ok", "message": "YouTube API شغالة"}


@app.get("/info")
def get_video_info(url: str = Query(..., description="رابط فيديو اليوتيوب")):
    """
    يرجع معلومات الفيديو + روابط التحميل المباشرة لكل جودة،
    من غير ما يحمل الفيديو على السيرفر (بيوفر Bandwidth وموارد).
    """
    ydl_opts = {
        "quiet": True,
        "no_warnings": True,
        "skip_download": True,
        "noplaylist": True,
    }

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"فشل استخراج بيانات الفيديو: {str(e)}")

    formats = []
    for f in info.get("formats", []):
        # نرجع بس الصيغ اللي فيها فيديو أو صوت فعلي وليها رابط مباشر
        if f.get("url") and (f.get("vcodec") != "none" or f.get("acodec") != "none"):
            formats.append({
                "format_id": f.get("format_id"),
                "ext": f.get("ext"),
                "resolution": f.get("resolution") or f.get("format_note"),
                "filesize": f.get("filesize") or f.get("filesize_approx"),
                "vcodec": f.get("vcodec"),
                "acodec": f.get("acodec"),
                "url": f.get("url"),
            })

    return {
        "title": info.get("title"),
        "duration": info.get("duration"),
        "thumbnail": info.get("thumbnail"),
        "uploader": info.get("uploader"),
        "formats": formats,
    }


@app.get("/best")
def get_best_link(url: str = Query(..., description="رابط فيديو اليوتيوب")):
    """
    يرجع أفضل رابط تحميل مباشر (فيديو + صوت مدمجين) بسرعة،
    مناسب لو عايز رابط واحد بس بدون قائمة الصيغ كلها.
    """
    ydl_opts = {
        "quiet": True,
        "no_warnings": True,
        "skip_download": True,
        "noplaylist": True,
        "format": "best[ext=mp4]/best",
    }

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"فشل استخراج الفيديو: {str(e)}")

    return {
        "title": info.get("title"),
        "duration": info.get("duration"),
        "thumbnail": info.get("thumbnail"),
        "download_url": info.get("url"),
        "ext": info.get("ext"),
    }
