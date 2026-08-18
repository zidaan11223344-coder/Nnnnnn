# Giant Chat Bot — Railway + Music

هذه النسخة مخصصة لـ **Giant Chat** وليست Telegram.

## لماذا تم تعديل الموسيقى؟
النسخة السابقة كانت تنزّل الصوت ثم تضعه في Supabase Storage وترسل رابط `media_url`.
على بعض الاستضافات/الإعدادات لا يكون الرابط قابلاً للوصول من تطبيق Giant Chat، أو يكون الصوت بصيغة WebM/M4A غير مناسبة لبعض مشغلات الصوت.

هذه النسخة:
1. تبحث عن الأغنية عبر Piped ثم yt-dlp.
2. تنزّل الصوت.
3. تحوّله إلى **MP3** إذا كان `ffmpeg` متاحاً.
4. تشغّل خادم HTTP داخل نفس خدمة Railway.
5. ترسل إلى Giant Chat رابطاً عاماً من نوع HTTPS.
6. ترسل الرسالة داخل Giant Chat كـ `message_type=voice`.

## Railway
ارفع المشروع إلى GitHub ثم اختره في Railway.

Variables:
- `SUPABASE_URL`
- `SUPABASE_KEY`
- `GIANT_USERNAME`
- `GIANT_PASSWORD`
- `OWNER_USERNAME` (اختياري)
- `PUBLIC_BASE_URL` (اختياري؛ إذا لم تضعه، يحاول البوت استخدام `RAILWAY_PUBLIC_DOMAIN` تلقائياً)

إذا لم يتوفر `RAILWAY_PUBLIC_DOMAIN`، بعد إنشاء Public Domain للخدمة ضع:
`PUBLIC_BASE_URL=https://your-domain.up.railway.app`

لا تحتاج إلى Telegram ولا Bot Token.

## أمر التشغيل
Dockerfile يشغل:
`python bot.py`

## أمر الأغنية داخل Giant Chat
`تشغيل اسم الأغنية`

أو:
`play اسم الأغنية`

## مهم
لا تضع كلمة مرور الحساب أو مفتاح Supabase داخل GitHub. استخدم Railway Variables.
