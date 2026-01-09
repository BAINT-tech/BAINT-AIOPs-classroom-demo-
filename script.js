const voiceBtn = document.getElementById("voiceBtn");
const subtitle = document.getElementById("subtitle");
const languageSelect = document.getElementById("language");

let speaking = false;

const explanations = {
  en: "Photosynthesis is the process plants use to make food using sunlight.",
  zh: "光合作用是植物利用阳光制造食物的过程。"
};

voiceBtn.addEventListener("click", () => {
  if (speaking) {
    speechSynthesis.cancel();
    speaking = false;
    voiceBtn.textContent = "🔊 Explain with Voice";
    return;
  }

  const lang = languageSelect.value;
  const text = explanations[lang];

  subtitle.textContent = text;

  const utterance = new SpeechSynthesisUtterance(text);
  utterance.lang = lang === "zh" ? "zh-CN" : "en-US";
  utterance.rate = 0.9;

  speaking = true;
  voiceBtn.textContent = "⏹ Stop Voice";

  utterance.onend = () => {
    speaking = false;
    voiceBtn.textContent = "🔊 Explain with Voice";
  };

  speechSynthesis.speak(utterance);
});

languageSelect.addEventListener("change", () => {
  subtitle.textContent = explanations[languageSelect.value];
  speechSynthesis.cancel();
  speaking = false;
  voiceBtn.textContent = "🔊 Explain with Voice";
});
