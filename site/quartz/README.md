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