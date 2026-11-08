// Cover the answers, as a reader would with a card; a click shows one.
const sample = document.querySelector(".sample");
const toggle = document.querySelector(".cover-toggle");
toggle.addEventListener("click", () => {
  const on = sample.classList.toggle("covered");
  toggle.setAttribute("aria-pressed", on);
  toggle.textContent = on ? "Show all answers" : "Cover the answers";
  sample.querySelectorAll(".frame.shown").forEach(f => f.classList.remove("shown"));
});
sample.addEventListener("click", e => {
  const a = e.target.closest(".covered .frame .a");
  if (a) a.parentElement.classList.add("shown");
});
