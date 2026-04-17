import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

optimized_mb            = 0.134483
unoptimized_mb          = 0.281206
optimized_heuristic_mb  = 0.199153
unoptimized_heuristic_mb = 0.239010
total = optimized_mb + unoptimized_mb + optimized_heuristic_mb + unoptimized_heuristic_mb

labels = ["Optimized", "Unoptimized", "Optimized + Heuristic", "Unoptimized + Heuristic"]
sizes  = [optimized_mb, unoptimized_mb, optimized_heuristic_mb, unoptimized_heuristic_mb]
colors = ["#1d8348", "#cb4335", "#a9cce3", "#e59866"]
explode = (0.04, 0.04, 0.04, 0.04)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 12,
})

fig, ax = plt.subplots(figsize=(10, 7))
fig.patch.set_facecolor("#fafafa")
ax.set_facecolor("#fafafa")

wedges, texts, autotexts = ax.pie(
    sizes,
    explode=explode,
    labels=None,
    colors=colors,
    autopct=lambda pct: f"{pct:.1f}%\n({pct/100*total:.2f} MB)",
    pctdistance=0.72,
    startangle=140,
    wedgeprops=dict(linewidth=2.5, edgecolor="#fafafa"),
    shadow=False,
)

for autotext in autotexts:
    autotext.set_fontsize(12)
    autotext.set_fontweight("bold")
    autotext.set_color("white")

centre_circle = plt.Circle((0, 0), 0.48, fc="#fafafa", linewidth=2.5, edgecolor="#fafafa")
ax.add_patch(centre_circle)

ax.text(0, 0.08, "Peak Memory", ha="center", va="center",
        fontsize=13, color="#555555", fontfamily="serif")
ax.text(0, -0.12, f"{total:.2f} MB", ha="center", va="center",
        fontsize=20, fontweight="bold", color="#1a1a1a", fontfamily="serif")
ax.text(0, -0.30, "total", ha="center", va="center",
        fontsize=11, color="#888888", fontfamily="serif")

legend_elements = [
    mpatches.Patch(facecolor=colors[0], label=f"Optimized — {optimized_mb:.4f} MB"),
    mpatches.Patch(facecolor=colors[1], label=f"Unoptimized — {unoptimized_mb:.4f} MB"),
    mpatches.Patch(facecolor=colors[2], label=f"Optimized + Heuristic — {optimized_heuristic_mb:.4f} MB"),
    mpatches.Patch(facecolor=colors[3], label=f"Unoptimized + Heuristic — {unoptimized_heuristic_mb:.4f} MB"),
]
ax.legend(
    handles=legend_elements,
    loc="lower center",
    bbox_to_anchor=(0, -0.12),
    frameon=False,
    fontsize=11,
    ncol=2,
    handlelength=1.2,
    handleheight=1.2,
)

ax.set_title(
    "Peak Memory Usage Comparison",
    fontsize=17,
    fontweight="bold",
    color="#1a1a1a",
    pad=24,
    fontfamily="serif",
)


plt.tight_layout()
plt.savefig("memory_comparison.png", dpi=300, bbox_inches="tight", facecolor=fig.get_facecolor())
plt.show()