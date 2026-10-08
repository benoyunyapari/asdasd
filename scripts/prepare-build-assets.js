'use strict';

const fs = require('node:fs/promises');
const path = require('node:path');
const sharp = require('sharp');

const projectRoot = path.resolve(__dirname, '..');
const outputRoot = path.join(projectRoot, 'buildassets', 'tier-sprites');
const transparent = { r: 0, g: 0, b: 0, alpha: 0 };
const families = {
  spike: ['base', 'core', 'rotor'],
  windmill: ['base', 'blades'],
  boost: ['base', 'arrows'],
  trap: ['base'],
  turret: ['base', 'head'],
  door: ['base'],
  heal: ['base'],
};

async function getTrimBounds(filePath) {
  const { info } = await sharp(filePath)
    .trim({ background: transparent, threshold: 0 })
    .png()
    .toBuffer({ resolveWithObject: true });

  if (!info.width || !info.height) throw new Error(`Sprite is fully transparent: ${filePath}`);
  return {
    left: Math.max(0, -info.trimOffsetLeft),
    top: Math.max(0, -info.trimOffsetTop),
    right: Math.max(0, -info.trimOffsetLeft) + info.width,
    bottom: Math.max(0, -info.trimOffsetTop) + info.height,
  };
}

async function buildTier(tier) {
  const sourceRoot = path.join(projectRoot, `tier${tier}builds`);
  const destination = path.join(outputRoot, `t${tier}`);
  await fs.mkdir(destination, { recursive: true });
  const expectedFiles = new Set();
  let builtCount = 0;

  for (const [family, parts] of Object.entries(families)) {
    const layers = [];
    for (const part of parts) {
      const fileName = `${family}_t${tier}_${part}.png`;
      const filePath = path.join(sourceRoot, fileName);
      try {
        await fs.access(filePath);
      } catch {
        continue;
      }
      const metadata = await sharp(filePath).metadata();
      if (metadata.width !== 4096 || metadata.height !== 4096) {
        throw new Error(`${filePath} must be a 4096x4096 source image.`);
      }
      layers.push({ part, filePath, bounds: await getTrimBounds(filePath) });
    }

    if (!layers.some(layer => layer.part === 'base')) {
      throw new Error(`Missing ${family} base sprite for tier ${tier}.`);
    }

    const crop = {
      left: Math.min(...layers.map(layer => layer.bounds.left)),
      top: Math.min(...layers.map(layer => layer.bounds.top)),
      right: Math.max(...layers.map(layer => layer.bounds.right)),
      bottom: Math.max(...layers.map(layer => layer.bounds.bottom)),
    };
    crop.width = crop.right - crop.left;
    crop.height = crop.bottom - crop.top;

    for (const layer of layers) {
      const outputName = `${family}-${layer.part}.webp`;
      expectedFiles.add(outputName);
      await sharp(layer.filePath)
        .extract({ left: crop.left, top: crop.top, width: crop.width, height: crop.height })
        .resize(256, 256, { fit: 'contain', background: transparent })
        .webp({ quality: 90, alphaQuality: 100, effort: 5 })
        .toFile(path.join(destination, outputName));
      builtCount++;
    }
    console.log(`  ${family}: ${layers.length} layers ready.`);
  }

  for (const fileName of await fs.readdir(destination)) {
    if (fileName.endsWith('.webp') && !expectedFiles.has(fileName)) {
      await fs.unlink(path.join(destination, fileName));
    }
  }
  return builtCount;
}

async function main() {
  let total = 0;
  for (let tier = 1; tier <= 6; tier++) {
    const built = await buildTier(tier);
    total += built;
    console.log(`Tier ${tier}: ${built} sprites ready.`);
  }
  console.log(`Built ${total} tiered build sprites in ${path.relative(projectRoot, outputRoot)}.`);
}

main().catch(error => {
  console.error('[Build assets]', error.message);
  process.exitCode = 1;
});