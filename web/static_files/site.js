// Wire the horizontal "taste of the maths" carousels: arrows scroll one card.
document.querySelectorAll(".carousel").forEach(function (carousel) {
  var track = carousel.querySelector(".carousel-track");
  if (!track) return;
  function step() { return Math.min(track.clientWidth * 0.85, 720); }
  var prev = carousel.querySelector(".carousel-arrow.prev");
  var next = carousel.querySelector(".carousel-arrow.next");
  if (prev) prev.addEventListener("click", function () {
    track.scrollBy({ left: -step(), behavior: "smooth" });
  });
  if (next) next.addEventListener("click", function () {
    track.scrollBy({ left: step(), behavior: "smooth" });
  });
});
