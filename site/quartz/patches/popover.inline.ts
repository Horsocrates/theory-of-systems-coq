import { computePosition, flip, inline, shift } from "@floating-ui/dom"
import { normalizeRelativeURLs } from "../../util/path"
import { fetchCanonical } from "./util"

const p = new DOMParser()
let activeAnchor: HTMLAnchorElement | null = null

// Contextual tabs: split popover content into tabs by H2 sections.
// Active tab = link anchor if present, else inferred from the current page slug, else the first tab.
function buildTabs(popoverInner: HTMLElement): ((hash: string) => void) | null {
  const firstH2 = popoverInner.querySelector("h2")
  if (!firstH2) return null
  const flow = firstH2.parentElement
  if (!flow) return null

  type Section = { title: string; id: string; nodes: Element[] }
  const sections: Section[] = []
  let current: Section = { title: "Общее", id: "", nodes: [] }
  for (const child of [...flow.children]) {
    if (child.tagName === "H2") {
      if (current.nodes.length > 0) sections.push(current)
      current = { title: child.textContent?.trim() ?? "", id: child.id, nodes: [child] }
    } else {
      current.nodes.push(child)
    }
  }
  sections.push(current)
  if (sections.length < 2) return null

  const wrappers: { title: string; id: string; wrapper: HTMLElement }[] = []
  for (const section of sections) {
    const wrapper = document.createElement("div")
    wrapper.classList.add("popover-tab-section")
    for (const node of section.nodes) wrapper.appendChild(node)
    flow.appendChild(wrapper)
    wrappers.push({ title: section.title, id: section.id, wrapper })
  }

  const tabBar = document.createElement("div")
  tabBar.classList.add("popover-tabs")
  const buttons: HTMLButtonElement[] = []
  const activate = (idx: number) => {
    wrappers.forEach((w, i) => w.wrapper.classList.toggle("active", i === idx))
    buttons.forEach((b, i) => b.classList.toggle("active", i === idx))
  }
  sections.forEach((section, i) => {
    const btn = document.createElement("button")
    btn.type = "button"
    btn.textContent = section.title
    btn.addEventListener("click", (e) => {
      e.preventDefault()
      e.stopPropagation()
      activate(i)
    })
    buttons.push(btn)
    tabBar.appendChild(btn)
  })
  flow.insertBefore(tabBar, flow.firstChild)

  return (hash: string) => {
    let idx = -1
    if (hash !== "") {
      const target = `popover-internal-${hash.slice(1)}`
      idx = wrappers.findIndex((w) => w.id === target)
    }
    if (idx === -1) {
      const slugSource =
        document.body.dataset.slug ?? decodeURIComponent(window.location.pathname)
      // context lives in the page name itself, not its folder — use the last path segment
      const lastSegment =
        slugSource
          .replace(/^\//, "")
          .split("/")
          .filter((s) => s.length > 0 && s !== "index")
          .pop() ?? ""
      const word = lastSegment.split(/[-_]/)[0].toLowerCase()
      const stem = word.length > 4 ? word.slice(0, word.length - 2) : word
      if (stem.length >= 3) {
        idx = wrappers.findIndex((w) => w.title.toLowerCase().includes(stem))
      }
    }
    activate(idx === -1 ? 0 : idx)
  }
}

async function mouseEnterHandler(
  this: HTMLAnchorElement,
  { clientX, clientY }: { clientX: number; clientY: number },
) {
  const link = (activeAnchor = this)
  if (link.dataset.noPopover === "true") {
    return
  }

  async function setPosition(popoverElement: HTMLElement) {
    const { x, y } = await computePosition(link, popoverElement, {
      strategy: "fixed",
      middleware: [inline({ x: clientX, y: clientY }), shift(), flip()],
    })
    Object.assign(popoverElement.style, {
      transform: `translate(${x.toFixed()}px, ${y.toFixed()}px)`,
    })
  }

  function showPopover(popoverElement: HTMLElement) {
    clearActivePopover()
    popoverElement.classList.add("active-popover")
    setPosition(popoverElement as HTMLElement)

    const selectTab = (popoverElement as any)._selectTab as ((hash: string) => void) | undefined
    if (selectTab) {
      selectTab(hash)
      return
    }

    if (hash !== "") {
      const inner = popoverElement.querySelector(".popover-inner") as HTMLElement | null
      if (inner) {
        const targetAnchor = `#popover-internal-${hash.slice(1)}`
        const heading = inner.querySelector(targetAnchor) as HTMLElement | null
        if (heading) {
          // leave ~12px of buffer when scrolling to a heading
          inner.scroll({ top: heading.offsetTop - 12, behavior: "instant" })
        }
      }
    }
  }

  const targetUrl = new URL(link.href)
  const hash = decodeURIComponent(targetUrl.hash)
  targetUrl.hash = ""
  targetUrl.search = ""
  const popoverId = `popover-${link.pathname}`
  const prevPopoverElement = document.getElementById(popoverId)

  // dont refetch if there's already a popover
  if (!!document.getElementById(popoverId)) {
    showPopover(prevPopoverElement as HTMLElement)
    return
  }

  const response = await fetchCanonical(targetUrl).catch((err) => {
    console.error(err)
  })

  if (!response) return
  const rawContentType = response.headers.get("Content-Type")
  if (!rawContentType) return
  const [contentType] = rawContentType.split(";")
  const [contentTypeCategory, typeInfo] = contentType.split("/")

  const popoverElement = document.createElement("div")
  popoverElement.id = popoverId
  popoverElement.classList.add("popover")
  const popoverInner = document.createElement("div")
  popoverInner.classList.add("popover-inner")
  popoverInner.dataset.contentType = contentType ?? undefined
  popoverElement.appendChild(popoverInner)

  switch (contentTypeCategory) {
    case "image":
      const img = document.createElement("img")
      img.src = targetUrl.toString()
      img.alt = targetUrl.pathname

      popoverInner.appendChild(img)
      break
    case "application":
      switch (typeInfo) {
        case "pdf":
          const pdf = document.createElement("iframe")
          pdf.src = targetUrl.toString()
          popoverInner.appendChild(pdf)
          break
        default:
          break
      }
      break
    default:
      const contents = await response.text()
      const html = p.parseFromString(contents, "text/html")
      normalizeRelativeURLs(html, targetUrl)
      // prepend all IDs inside popovers to prevent duplicates
      html.querySelectorAll("[id]").forEach((el) => {
        const targetID = `popover-internal-${el.id}`
        el.id = targetID
      })
      const elts = [...html.getElementsByClassName("popover-hint")]
      if (elts.length === 0) return

      elts.forEach((elt) => popoverInner.appendChild(elt))

      const selectTab = buildTabs(popoverInner)
      if (selectTab) {
        ;(popoverElement as any)._selectTab = selectTab
      }
  }

  if (!!document.getElementById(popoverId)) {
    return
  }

  document.body.appendChild(popoverElement)
  if (activeAnchor !== this) {
    return
  }

  showPopover(popoverElement)
}

function clearActivePopover() {
  activeAnchor = null
  const allPopoverElements = document.querySelectorAll(".popover")
  allPopoverElements.forEach((popoverElement) => popoverElement.classList.remove("active-popover"))
}

function setupPopovers() {
  const links = [...document.querySelectorAll("a.internal")] as HTMLAnchorElement[]
  for (const link of links) {
    link.addEventListener("mouseenter", mouseEnterHandler)
    link.addEventListener("mouseleave", clearActivePopover)
    window.addCleanup(() => {
      link.removeEventListener("mouseenter", mouseEnterHandler)
      link.removeEventListener("mouseleave", clearActivePopover)
    })
  }
}

document.addEventListener("nav", setupPopovers)
document.addEventListener("render", setupPopovers)
