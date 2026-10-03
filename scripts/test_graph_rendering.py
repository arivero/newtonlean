"""Regressions for malformed SVGs and evidence status lost in raster figures."""
from pathlib import Path
import runpy
import shutil
import tempfile
from types import SimpleNamespace
import xml.etree.ElementTree as ET

root = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory(prefix='newton-graph-rendering-') as tmp:
    work = Path(tmp)
    (work / 'scripts').mkdir()
    (work / 'research').mkdir()
    shutil.copy2(root / 'scripts/plot_graphs.py', work / 'scripts')
    shutil.copy2(root / 'research/dependencies.json', work / 'research')
    renderer = runpy.run_path(str(work / 'scripts/plot_graphs.py'))
    svgs = sorted((work / 'docs/graphs').glob('*.svg'))
    assert len(svgs) == 7, f'expected seven SVGs, got {len(svgs)}'
    for path in svgs:
        ET.parse(path)
    print('Passed XML parsing for all seven generated SVGs')

    try:
        from PIL import Image, ImageChops, ImageColor
    except ImportError:
        print('Raster regressions skipped: Pillow is unavailable')
    else:
        left = SimpleNamespace(x=20, y=80, w=20, h=40, cy=100,
                               stage='1687', refs=[], lines=['A'])
        right = SimpleNamespace(x=140, y=80, w=20, h=40, cy=100,
                                stage='1687', refs=[], lines=['B'])
        colour = ImageColor.getrgb('#33475b')
        strokes = []
        for status in ('explicit_dependency', 'implicit_dependency',
                       'editorial_interpretation', 'modern_reconstruction'):
            path = work / f'{status}.png'
            edge = {'relation': 'proof_dependency', 'status': status}
            renderer['to_png'](path, 'Status regression', '', {'A': left, 'B': right},
                               [(edge, left, right)], 640, 200)
            with Image.open(path) as img:
                stroke = tuple(img.getpixel((x, 100)) for x in range(60, 120))
                strokes.append(stroke)
                pixels = set(stroke)
                if status == 'explicit_dependency':
                    assert pixels == {colour}, (status, pixels)
                else:
                    assert colour in pixels and (255, 255, 255) in pixels, (status, pixels)
                footer = img.crop((0, 200, img.width, img.height))
                white = Image.new('RGB', footer.size, 'white')
                assert ImageChops.difference(footer, white).getbbox(), 'missing raster legend'
        assert len(set(strokes)) == 4, 'evidence statuses must have distinct raster patterns'
        assert len(list((work / 'docs/graphs').glob('*.png'))) == 7
        assert (work / 'docs/graphs/all-graphs.pdf').is_file()
        print('Passed solid/dashed/dotted/dash-dot raster edges and legend checks')
