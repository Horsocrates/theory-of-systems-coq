# sync-to-repo.ps1 — copy the site SOURCE (content + config + core patches + pipeline scripts)
# into the theory-of-systems-coq repo at site\quartz\, so it is versioned and OneDrive-backed.
# The Quartz install itself (node_modules, .quartz) stays outside OneDrive on purpose.
#
# Restore procedure is documented in site\quartz\README.md (written by this script).

$ErrorActionPreference = "Stop"
$src  = $PSScriptRoot
$dest = "C:\Users\abary\OneDrive\Desktop\theory-of-systems-coq\site\quartz"

New-Item -ItemType Directory -Force "$dest" | Out-Null
New-Item -ItemType Directory -Force "$dest\patches" | Out-Null
New-Item -ItemType Directory -Force "$dest\patches\note-properties" | Out-Null
New-Item -ItemType Directory -Force "$dest\patches\folder-page" | Out-Null
New-Item -ItemType Directory -Force "$dest\patches\crawl-links" | Out-Null
New-Item -ItemType Directory -Force "$dest\patches\bases-page" | Out-Null
New-Item -ItemType Directory -Force "$dest\patches\graph" | Out-Null
New-Item -ItemType Directory -Force "$dest\patches\breadcrumbs" | Out-Null
New-Item -ItemType Directory -Force "$dest\tools" | Out-Null
New-Item -ItemType Directory -Force "$dest\tables" | Out-Null
New-Item -ItemType Directory -Force "$dest\styles" | Out-Null
New-Item -ItemType Directory -Force "$dest\static-fonts" | Out-Null

# config + package manifests (lock-файлы пиннят версии — патчи dist привязаны к ним)
Copy-Item "$src\quartz.config.yaml"  "$dest\" -Force
Copy-Item "$src\package.json"        "$dest\" -Force
Copy-Item "$src\package-lock.json"   "$dest\" -Force
Copy-Item "$src\quartz.lock.json"    "$dest\" -Force

# ВЕСЬ конвейер (build + генерация тома и каталогов) — раньше терялись 7 из 9
$scripts = @(
  "deploy.ps1", "sync-to-repo.ps1",
  "tex2md.ps1", "batch_tom.ps1", "tom_concepts.ps1", "tom_nav.ps1", "tom_mentions.ps1",
  "catalog2md.ps1", "dump_xlsx.ps1", "knowledge_import.ps1"
)
foreach ($s in $scripts) { Copy-Item "$src\$s" "$dest\" -Force }
Copy-Item "$src\tools\linkcheck.cjs" "$dest\tools\" -Force
Copy-Item "$src\tools\patch-graph-cyrillic.cjs" "$dest\tools\" -Force
Copy-Item "$src\tools\highlights2md.ps1"     "$dest\tools\" -Force
Copy-Item "$src\tools\highlights-vitrina.md" "$dest\tools\" -Force

# TSV-таблицы (производные от docs\*.xlsx, но нужны tom_mentions/catalog2md без Excel)
Copy-Item "$src\tables\*.tsv" "$dest\tables\" -Force

# content (mirror)
if (Test-Path "$dest\content") { Remove-Item "$dest\content" -Recurse -Force -Confirm:$false }
Copy-Item "$src\content" "$dest\content" -Recurse -Force

# patched Quartz core files (popover tabs)
Copy-Item "$src\quartz\components\scripts\popover.inline.ts" "$dest\patches\popover.inline.ts" -Force
Copy-Item "$src\quartz\components\styles\popover.scss"       "$dest\patches\popover.scss" -Force

# тема «Классический том»: пользовательские стили + самохостимые шрифты (PT Serif/PT Sans)
Copy-Item "$src\quartz\styles\custom.scss" "$dest\styles\custom.scss" -Force
Copy-Item "$src\quartz\styles\fonts.scss"  "$dest\styles\fonts.scss"  -Force
Copy-Item "$src\quartz\static\fonts\*.woff2" "$dest\static-fonts\" -Force

# patched note-properties plugin dist (ru labels + column width + folder-link resolver) — plugin update overwrites
Copy-Item "$src\.quartz\plugins\note-properties\dist\index.js" `
          "$dest\patches\note-properties\index.js" -Force
Copy-Item "$src\.quartz\plugins\note-properties\dist\components\index.js" `
          "$dest\patches\note-properties\components-index.js" -Force

# patched folder-page plugin dist (alphabetical listing, no dates, suppressed folder indexes
# исключены и из авто-листинга — suppressedFolderPages) — plugin update overwrites
Copy-Item "$src\.quartz\plugins\folder-page\dist\index.js" `
          "$dest\patches\folder-page\index.js" -Force
Copy-Item "$src\.quartz\plugins\folder-page\dist\components\index.js" `
          "$dest\patches\folder-page\components-index.js" -Force

# patched breadcrumbs plugin dist (крошки подавленных папок — текст без ссылки) — plugin update overwrites
Copy-Item "$src\.quartz\plugins\breadcrumbs\dist\index.js" `
          "$dest\patches\breadcrumbs\index.js" -Force
Copy-Item "$src\.quartz\plugins\breadcrumbs\dist\components\index.js" `
          "$dest\patches\breadcrumbs\components-index.js" -Force

# patched crawl-links plugin dist (folder-link resolver: [[Папка]] -> папка/index) — plugin update overwrites
Copy-Item "$src\.quartz\plugins\crawl-links\dist\index.js" `
          "$dest\patches\crawl-links\index.js" -Force

# patched bases-page plugin dist chunk (same resolver fix) — plugin update overwrites
Copy-Item "$src\.quartz\plugins\bases-page\dist\chunk-X2AZ5GOJ.js" `
          "$dest\patches\bases-page\chunk-X2AZ5GOJ.js" -Force

# patched graph plugin dist (decodeURIComponent for Cyrillic slugs) — plugin update overwrites.
# Патч накладывается СКРИПТОМ (tools\patch-graph-cyrillic.cjs), т.к. он идемпотентен и переживает
# смену минифицированных имён; копии dist — на случай, если строка-цель изменится.
Copy-Item "$src\.quartz\plugins\graph\dist\index.js" `
          "$dest\patches\graph\index.js" -Force
Copy-Item "$src\.quartz\plugins\graph\dist\components\index.js" `
          "$dest\patches\graph\components-index.js" -Force

# restore instructions
$readme = @'
# site/quartz — исходники сайта «Путь Мудрости» (Quartz v5)

Источник истины живёт в C:\Users\abary\quartz-put-mudrosti (вне OneDrive: node_modules).
Эта папка — версионируемая копия: контент, конфиг, патчи ядра/плагинов и ВЕСЬ конвейер
генерации (том из LaTeX, каталоги из xlsx). Обновляется скриптом sync-to-repo.ps1.

## Восстановление с нуля

1. Node.js LTS (portable): C:\Users\abary\AppData\Local\Programs\node-v24.18.0-win-x64
   (prepend to PATH).
2. Новая папка ВНЕ OneDrive, в ней: `npx quartz create` (Quartz v5) либо клон quartz v5;
   затем `npm i` (package.json + package-lock.json отсюда — версии пиннены).
3. Скопировать quartz.config.yaml, content\, все *.ps1, tools\, tables\ из этой папки;
   дизайн: styles\custom.scss и styles\fonts.scss -> quartz\styles\,
   static-fonts\*.woff2 -> quartz\static\fonts\ (самохостинг PT Serif/PT Sans).
4. `npx quartz plugin install` — один раз (иначе build падает: "Could not resolve ../../.quartz/plugins");
   quartz.lock.json отсюда пиннит версии плагинов.
5. Наложить патчи (ЛЮБОЕ обновление плагина/ядра их перезаписывает — после обновления повторить):
   - patches\popover.inline.ts  -> quartz\components\scripts\popover.inline.ts   (вкладки в поповерах)
   - patches\popover.scss       -> quartz\components\styles\popover.scss         (стили вкладок)
   - patches\note-properties\index.js            -> .quartz\plugins\note-properties\dist\index.js
   - patches\note-properties\components-index.js -> .quartz\plugins\note-properties\dist\components\index.js
     (русские подписи Свойства/Описание/Теги/Синонимы + ширина колонки 9rem + резолвер папок)
   - patches\folder-page\index.js            -> .quartz\plugins\folder-page\dist\index.js
   - patches\folder-page\components-index.js -> .quartz\plugins\folder-page\dist\components\index.js
     (листинг папки: алфавитная сортировка вместо даты, дата не рендерится; плюс список
      suppressedFolderPages — подавленные индексы корпусов (том-математика, теория-знания,
      том-эпистемология) не попадают ни в virtualPages, ни в авто-листинг родителя)
   - patches\breadcrumbs\index.js            -> .quartz\plugins\breadcrumbs\dist\index.js
   - patches\breadcrumbs\components-index.js -> .quartz\plugins\breadcrumbs\dist\components\index.js
     (хлебные крошки: для папок из того же списка suppressedFolderPages крошка рендерится
      текстом-span без ссылки — иначе крошка вела на несуществующий индекс, 3 мёртвые ссылки)
   - patches\crawl-links\index.js -> .quartz\plugins\crawl-links\dist\index.js
     (КРИТИЧНО: резолвер [[Папка]] -> папка/index; без него ~700 битых ссылок — [[Направления]],
      [[Каталог ошибок]], [[Том Математика]] падают в корень; суть патча: в одно-сегментной ветке
      "shortest" цель дополнительно матчится с parts.at(-2), когда последний сегмент слага = "index")
   - patches\bases-page\chunk-X2AZ5GOJ.js -> .quartz\plugins\bases-page\dist\chunk-X2AZ5GOJ.js
     (тот же резолвер-фикс; имя чанка может смениться при обновлении плагина — искать по
      "parts.at(-1)" и накладывать вручную)
   - ГРАФ, кириллица: `node tools\patch-graph-cyrillic.cjs` (идемпотентен, ставит оба бандла
     graph\dist\index.js и graph\dist\components\index.js). Суть: getFullSlugFromUrl читал
     window.location.pathname БЕЗ decodeURIComponent — на кириллическом слаге браузер отдаёт
     percent-encoded путь, а ключи contentIndex в кириллице, поэтому текущая страница не
     находилась в данных: локальный граф вырождался в ОДИН узел, подписанный сырым
     «%D0%B1%D0%B8...», без связей (и «посещённые» узлы не подсвечивались никогда).
     Копии пропатченных бандлов — в patches\graph\ на случай, если строка-цель изменится.
     NB: тем же болен плагин stacked-pages (сейчас enabled: false) — при включении починить так же.
6. Сборка: deploy.ps1 (см. шапку). Дев-сервер: `.\deploy.ps1 -Serve` -> http://localhost:8080.
   deploy.ps1 после сборки сам гоняет tools\linkcheck.cjs — если патч п.5 слетел,
   сборка «упадёт» на ~700 битых ссылках, это сигнал переналожить патчи.

## Дизайн (тема «Классический том», 2026-07-16)

- Палитра (светлая/тёмная) и имена шрифтов — quartz.config.yaml (theme.colors, theme.typography
  И опции плагина fonts — менять СИНХРОННО в обоих местах).
- Вся тема — quartz\styles\custom.scss (подключается вне @layer quartz-base, переопределения
  надёжны); @font-face — quartz\styles\fonts.scss; woff2 — quartz\static\fonts\.
- Разметка главной (эпиграф-герой + карточки направлений) — raw-HTML в content\index.md;
  классы .home-hero/.epigraph/.directions/.card стилизуются из custom.scss.

## Регенерация контента

- Том «Математика» из LaTeX: batch_tom.ps1 (тянет функции из ЛОКАЛЬНОГО tex2md.ps1),
  затем ОБЯЗАТЕЛЬНО по порядку: tom_concepts.ps1 -> tom_nav.ps1 -> tom_mentions.ps1.
- Каталоги из xlsx: dump_xlsx.ps1 (docs\*.xlsx -> tables\*.tsv, нужен Excel) -> catalog2md.ps1.
  Без Excel: tables\*.tsv уже лежат здесь.

## Деплой

`.\deploy.ps1 -BaseUrl "<домен>"` -> public\ — самодостаточная статика
(+ авто-проверки: линк-чек и «нет localhost в sitemap/RSS»).
- VPS (nginx): выгрузить public\* в web root; нужен try_files $uri $uri.html $uri/ =404.
- GitHub Pages: выгрузить public\* в ветку Pages. ВНИМАНИЕ: public\CNAME сейчас пишется
  из baseUrl — проверить содержимое перед пушем (для VPS плагин cname лучше выключить).
Выбор хостинга — открытое решение автора.
'@
$enc = New-Object System.Text.UTF8Encoding($false)
[System.IO.File]::WriteAllText("$dest\README.md", $readme, $enc)

Write-Host "synced -> $dest"

