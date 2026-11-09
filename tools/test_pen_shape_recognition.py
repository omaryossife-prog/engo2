"""Small regression test for Engo's freehand shape recognizer.

Run from the project root with the app's Python environment:
    python tools/test_pen_shape_recognition.py
"""
import math
import sys
from pathlib import Path

import fitz

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from engo_widgets import _recognize_pen_shape


def square_trace(wobble=4.0):
    points = []
    sides = [
        ((100, 100), (200, 100)),
        ((200, 100), (200, 200)),
        ((200, 200), (100, 200)),
        ((100, 200), (100, 100)),
    ]
    for side, ((x0, y0), (x1, y1)) in enumerate(sides):
        for i in range(50):
            t = i / 50
            offset = wobble * math.sin(i * 1.7 + side * 0.6)
            if side in (0, 2):
                points.append(fitz.Point(x0 + (x1 - x0) * t, y0 + (y1 - y0) * t + offset))
            else:
                points.append(fitz.Point(x0 + (x1 - x0) * t + offset, y0 + (y1 - y0) * t))
    points.append(points[0])
    return points


def circle_trace(radius_wobble=6.0, aspect=1.0):
    points = []
    for i in range(101):
        angle = i * 2 * math.pi / 100
        radius = 50 + radius_wobble * math.sin(i * 3.71)
        points.append(fitz.Point(
            150 + radius * math.cos(angle),
            150 + (radius / aspect) * math.sin(angle),
        ))
    return points


def main():
    cases = [
        ("wobbly square", square_trace(), "square"),
        ("rough circle", circle_trace(), "circle"),
        ("wide oval", circle_trace(radius_wobble=2.0, aspect=2.4), "circle"),
    ]
    for label, points, expected in cases:
        result = _recognize_pen_shape(points)
        actual = result.get("kind") if result else None
        print(f"{label}: {actual}")
        if actual != expected:
            raise SystemExit(f"FAIL: {label} should be recognized as {expected}, got {actual}")
    print("PASS: freehand square/circle/oval regression checks")


if __name__ == "__main__":
    main()
