/**
 * NetworkPhysics.js - Moomoo.io & Starve.io Grade Networked 2D Physics Engine
 * 
 * Provides:
 * 1. Penetration Resolution: Mass-weighted separation vector calculation for Circle-Circle
 *    and Circle-Box (AABB / OBB) with ZERO pixel clipping.
 * 2. Velocity Projection & Smooth Sliding: Vector projection onto surface tangents
 *    preventing speed stalls and jitter when pressing against solid colliders.
 * 3. Smooth Server Reconciliation: Error-offset exponential decay and frame-by-frame
 *    lerp reconcilers that eliminate snapping and visual rubber-banding.
 * 
 * Compatible with Node.js (CommonJS) and Modern Browsers (ES / Global).
 */

(function (root, factory) {
  if (typeof module === 'object' && module.exports) {
    // Node.js CommonJS
    module.exports = factory();
  } else {
    // Browser Global
    root.NetworkPhysics = factory();
  }
}(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  // Reusable collision result object to avoid garbage collection overhead in hot loops
  const _sharedCol = {
    collided: false,
    nx: 0,
    ny: 0,
    depth: 0
  };

  /**
   * 1. Penetration Resolution: Circle vs Circle
   * Calculates exact overlap depth and collision normal, then pushes entities
   * apart strictly proportional to their inverse masses (w = 1 / mass).
   * 
   * @param {Object} posA - { x, y }
   * @param {number} radiusA
   * @param {number} invMassA - 0 = immovable/static, >0 = dynamic (e.g. 1.0)
   * @param {Object} posB - { x, y }
   * @param {number} radiusB
   * @param {number} invMassB - 0 = immovable/static, >0 = dynamic (e.g. 1.0)
   * @param {Object} [out] - Optional reusable output object
   * @returns {Object|null} Collision normal (pointing from B to A) & overlap depth
   */
  function resolveCircleCircle(posA, radiusA, invMassA, posB, radiusB, invMassB, out) {
    const dx = posA.x - posB.x;
    const dy = posA.y - posB.y;
    const distSq = dx * dx + dy * dy;
    const minDist = radiusA + radiusB;

    if (distSq >= minDist * minDist) {
      if (out) out.collided = false;
      return null;
    }

    const dist = Math.sqrt(distSq);
    // Degenerate case guard (exact same coordinate)
    const nx = dist > 1e-6 ? dx / dist : 1.0;
    const ny = dist > 1e-6 ? dy / dist : 0.0;
    const depth = minDist - (dist > 1e-6 ? dist : 0.0);

    const totalInvMass = invMassA + invMassB;
    if (totalInvMass <= 1e-6) {
      // Both are static; cannot resolve
      if (out) out.collided = false;
      return null;
    }

    // Proportional separation vector
    const ratioA = invMassA / totalInvMass;
    const ratioB = invMassB / totalInvMass;

    if (ratioA > 0) {
      posA.x += nx * depth * ratioA;
      posA.y += ny * depth * ratioA;
    }
    if (ratioB > 0) {
      posB.x -= nx * depth * ratioB;
      posB.y -= ny * depth * ratioB;
    }

    const res = out || _sharedCol;
    res.collided = true;
    res.nx = nx;
    res.ny = ny;
    res.depth = depth;
    return res;
  }

  /**
   * 1b. Penetration Resolution: Circle vs Box (AABB or Rotated OBB)
   * Handles static/dynamic boxes (walls, buildings, crates, spikes).
   * 
   * @param {Object} circlePos - { x, y }
   * @param {number} radius - Circle radius
   * @param {number} circleInvMass - e.g. 1.0
   * @param {Object} box - { x, y, width, height, angle (optional), isStatic, invMass }
   * @param {Object} [out] - Optional reusable output object
   * @returns {Object|null}
   */
  function resolveCircleBox(circlePos, radius, circleInvMass, box, out) {
    const hw = (box.width || box.size || 50) * 0.5;
    const hh = (box.height || box.size || 50) * 0.5;
    const angle = box.angle || 0;
    const boxInvMass = box.invMass !== undefined ? box.invMass : (box.isStatic || box.isStatic !== false ? 0.0 : 1.0);

    let localX, localY;
    let cos = 1, sin = 0;

    if (angle !== 0) {
      cos = Math.cos(-angle);
      sin = Math.sin(-angle);
      const relX = circlePos.x - box.x;
      const relY = circlePos.y - box.y;
      localX = relX * cos - relY * sin;
      localY = relX * sin + relY * cos;
    } else {
      localX = circlePos.x - box.x;
      localY = circlePos.y - box.y;
    }

    // Closest point on box in local space
    const cx = Math.max(-hw, Math.min(hw, localX));
    const cy = Math.max(-hh, Math.min(hh, localY));

    const dx = localX - cx;
    const dy = localY - cy;
    const distSq = dx * dx + dy * dy;

    let localNx = 0, localNy = 0, depth = 0;

    if (distSq > 1e-8) {
      if (distSq >= radius * radius) {
        if (out) out.collided = false;
        return null;
      }
      const dist = Math.sqrt(distSq);
      localNx = dx / dist;
      localNy = dy / dist;
      depth = radius - dist;
    } else {
      // Circle center is inside the box: find shortest distance to one of the 4 borders
      const dLeft = localX - (-hw);
      const dRight = hw - localX;
      const dTop = localY - (-hh);
      const dBottom = hh - localY;

      const minEdge = Math.min(dLeft, dRight, dTop, dBottom);
      if (minEdge === dLeft) { localNx = -1; localNy = 0; }
      else if (minEdge === dRight) { localNx = 1; localNy = 0; }
      else if (minEdge === dTop) { localNx = 0; localNy = -1; }
      else { localNx = 0; localNy = 1; }
      depth = radius + minEdge;
    }

    // Transform collision normal back to world space
    let worldNx = localNx;
    let worldNy = localNy;
    if (angle !== 0) {
      const worldCos = Math.cos(angle);
      const worldSin = Math.sin(angle);
      worldNx = localNx * worldCos - localNy * worldSin;
      worldNy = localNx * worldSin + localNy * worldCos;
    }

    const totalInvMass = circleInvMass + boxInvMass;
    if (totalInvMass <= 1e-6) {
      if (out) out.collided = false;
      return null;
    }

    const ratioCircle = circleInvMass / totalInvMass;
    const ratioBox = boxInvMass / totalInvMass;

    if (ratioCircle > 0) {
      circlePos.x += worldNx * depth * ratioCircle;
      circlePos.y += worldNy * depth * ratioCircle;
    }
    if (ratioBox > 0) {
      box.x -= worldNx * depth * ratioBox;
      box.y -= worldNy * depth * ratioBox;
    }

    const res = out || _sharedCol;
    res.collided = true;
    res.nx = worldNx;
    res.ny = worldNy;
    res.depth = depth;
    return res;
  }

  /**
   * Unified Generic Collision Resolver
   * Dispatches to Circle-Circle or Circle-Box based on entity properties.
   */
  function resolveCollision(entityA, entityB, options = {}) {
    const isBoxA = entityA.shape === 'box' || (entityA.width && entityA.height && !entityA.radius);
    const isBoxB = entityB.shape === 'box' || (entityB.width && entityB.height && !entityB.radius);

    const invA = entityA.invMass !== undefined ? entityA.invMass : (entityA.isStatic ? 0 : (entityA.mass ? 1 / entityA.mass : 1.0));
    const invB = entityB.invMass !== undefined ? entityB.invMass : (entityB.isStatic ? 0 : (entityB.mass ? 1 / entityB.mass : 1.0));

    let col = null;

    if (!isBoxA && !isBoxB) {
      const rA = entityA.radius || 34;
      const rB = entityB.radius || 34;
      col = resolveCircleCircle(entityA, rA, invA, entityB, rB, invB, options.out);
    } else if (!isBoxA && isBoxB) {
      const rA = entityA.radius || 34;
      col = resolveCircleBox(entityA, rA, invA, entityB, options.out);
    } else if (isBoxA && !isBoxB) {
      const rB = entityB.radius || 34;
      col = resolveCircleBox(entityB, rB, invB, entityA, options.out);
      if (col) {
        // Invert normal so it points from B to A
        col.nx = -col.nx;
        col.ny = -col.ny;
      }
    }

    // Smooth Velocity Sliding (if velocity projection requested and velocities exist)
    if (col && col.collided && options.slide !== false) {
      const friction = options.friction !== undefined ? options.friction : 0.0;
      if (entityA.vx !== undefined && entityA.vy !== undefined) {
        projectVelocitySlide(entityA, col.nx, col.ny, friction);
      }
      if (entityB.vx !== undefined && entityB.vy !== undefined) {
        // Entity B normal is opposite (-nx, -ny)
        projectVelocitySlide(entityB, -col.nx, -col.ny, friction);
      }
    }

    return col;
  }

  /**
   * 2. Velocity Projection & Smooth Sliding
   * Decomposes the velocity vector into normal and tangential components.
   * If the entity is moving INTO the obstacle surface (dot < 0), the normal
   * component is eliminated, allowing smooth sliding along the tangent vector.
   * 
   * @param {Object} vel - { vx, vy } or { x, y }
   * @param {number} nx - Surface normal X (pointing out of obstacle toward entity)
   * @param {number} ny - Surface normal Y
   * @param {number} [friction=0.0] - Tangential friction coefficient [0.0 = ice, 1.0 = halt]
   * @returns {boolean} True if sliding projection was applied
   */
  function projectVelocitySlide(vel, nx, ny, friction = 0.0) {
    const isNamed = vel.vx !== undefined;
    const vx = isNamed ? vel.vx : vel.x;
    const vy = isNamed ? vel.vy : vel.y;

    // Normal velocity component (dot product)
    const normalVel = vx * nx + vy * ny;

    // Only cancel velocity if moving TOWARD the obstacle surface
    if (normalVel < 0) {
      let newVx = vx - normalVel * nx;
      let newVy = vy - normalVel * ny;

      if (friction > 0) {
        const f = Math.min(1.0, Math.max(0.0, friction));
        newVx *= (1.0 - f);
        newVy *= (1.0 - f);
      }

      if (isNamed) {
        vel.vx = newVx;
        vel.vy = newVy;
      } else {
        vel.x = newVx;
        vel.y = newVy;
      }
      return true;
    }
    return false;
  }

  /**
   * 3. Smooth Server Reconciliation Engine
   * 
   * Provides two production-ready modes to eliminate jitter / rubber-banding:
   * 
   * Mode A: Error Offset Exponential Decay (Industry Standard)
   * - Immediately sets the simulation coordinate to the server's authoritative position.
   * - Preserves the visual position seamlessly by placing the difference into a render error offset.
   * - Exponentially decays the render error offset to 0 over ~100-150ms.
   * - Result: ZERO visual snap on the frame of correction!
   * 
   * Mode B: Frame-by-Frame Lerp Correction (10% - 20% Convergence)
   * - Progressively shifts the client position towards the server target by a smooth factor every frame.
   */
  class SmoothReconciler {
    /**
     * @param {Object} options
     * @param {number} [options.decayRate=20.0] - Exponential decay speed for error offset (1/sec)
     * @param {number} [options.lerpFactor=0.15] - Target lerp factor per frame (10% - 20%)
     * @param {number} [options.snapThreshold=350] - Teleport/respawn threshold in world units
     * @param {string} [options.mode='error_decay'] - 'error_decay' or 'target_lerp'
     */
    constructor(options = {}) {
      this.decayRate = options.decayRate || 20.0;
      this.lerpFactor = options.lerpFactor || 0.15;
      this.snapThreshold = options.snapThreshold || 650.0;
      this.mode = options.mode || 'error_decay';

      // Visual Error Offset Accumulator (Mode A)
      this.renderErrX = 0.0;
      this.renderErrY = 0.0;

      // Server Target Coordinates (Mode B)
      this.targetX = null;
      this.targetY = null;
    }

    /**
     * Called when a server authoritative position packet arrives (e.g. pos_correction, self_state).
     * 
     * @param {Object} simPos - Player simulation position { x, y }
     * @param {number} serverX - Server authoritative X
     * @param {number} serverY - Server authoritative Y
     */
    onServerPacket(simPos, serverX, serverY) {
      if (!Number.isFinite(serverX) || !Number.isFinite(serverY)) return;

      const dx = simPos.x - serverX;
      const dy = simPos.y - serverY;
      const distSq = dx * dx + dy * dy;

      // Teleport or respawn: hard snap immediately
      if (distSq > this.snapThreshold * this.snapThreshold) {
        simPos.x = serverX;
        simPos.y = serverY;
        this.renderErrX = 0.0;
        this.renderErrY = 0.0;
        this.targetX = serverX;
        this.targetY = serverY;
        return;
      }

      if (this.mode === 'error_decay') {
        // Industry Standard: Authoritative snap in simulation + seamless visual error accumulator
        // Visual position = simPos.x + renderErrX
        // Before: visual = simPos.x + renderErrX
        // After server snap: simPos.x = serverX, renderErrX = renderErrX + (oldSimX - serverX)
        // New visual = serverX + renderErrX + (oldSimX - serverX) = oldSimX + renderErrX (0 PIXEL JUMP!)
        this.renderErrX += dx;
        this.renderErrY += dy;

        // Clamp max error accumulator to prevent accumulation runaway under severe packet loss
        const maxErr = 300;
        this.renderErrX = Math.max(-maxErr, Math.min(maxErr, this.renderErrX));
        this.renderErrY = Math.max(-maxErr, Math.min(maxErr, this.renderErrY));

        simPos.x = serverX;
        simPos.y = serverY;
      } else {
        // Target Lerp Mode
        this.targetX = serverX;
        this.targetY = serverY;
      }
    }

    /**
     * Called every physics/render frame to smoothly decay error or lerp position.
     * 
     * @param {Object} simPos - { x, y }
     * @param {number} dt - Delta time in seconds (e.g. 0.0166) or frame-scale
     */
    update(simPos, dt = 0.0166) {
      // Auto-detect and convert frame-scaled dt (~1.0) to seconds (~0.0166s)
      const dtSec = dt > 0.4 ? (dt / 60.0) : Math.max(0.001, dt);
      if (this.mode === 'error_decay') {
        if (Math.abs(this.renderErrX) > 0.001 || Math.abs(this.renderErrY) > 0.001) {
          const decay = Math.exp(-this.decayRate * dtSec);
          this.renderErrX *= decay;
          this.renderErrY *= decay;

          if (Math.abs(this.renderErrX) < 0.02) this.renderErrX = 0.0;
          if (Math.abs(this.renderErrY) < 0.02) this.renderErrY = 0.0;
        }
      } else {
        // Target Lerp mode
        if (this.targetX !== null && this.targetY !== null) {
          const dx = this.targetX - simPos.x;
          const dy = this.targetY - simPos.y;
          const distSq = dx * dx + dy * dy;

          if (distSq > this.snapThreshold * this.snapThreshold) {
            simPos.x = this.targetX;
            simPos.y = this.targetY;
            this.targetX = null;
            this.targetY = null;
          } else if (distSq > 0.01) {
            // Frame-independent rate or requested 10%-20% lerp
            const f = 1 - Math.pow(1 - this.lerpFactor, dt * 60);
            simPos.x += dx * f;
            simPos.y += dy * f;
          } else {
            simPos.x = this.targetX;
            simPos.y = this.targetY;
            this.targetX = null;
            this.targetY = null;
          }
        }
      }
    }

    /**
     * Retrieves the silky-smooth visual render position for camera and sprite drawing.
     * 
     * @param {Object} simPos - { x, y }
     * @param {Object} [out] - Optional { x, y } to receive coordinates
     * @returns {Object} Smooth render coordinates { x, y }
     */
    getRenderPos(simPos, out) {
      const res = out || { x: 0, y: 0 };
      if (this.mode === 'error_decay') {
        res.x = simPos.x + this.renderErrX;
        res.y = simPos.y + this.renderErrY;
      } else {
        res.x = simPos.x;
        res.y = simPos.y;
      }
      return res;
    }

    /**
     * Resets reconciler states (e.g. on respawn)
     */
    reset() {
      this.renderErrX = 0.0;
      this.renderErrY = 0.0;
      this.targetX = null;
      this.targetY = null;
    }
  }

  /**
   * Helper: Multi-iteration collision relaxation solver.
   * Runs N passes against an array of colliders to ensure zero penetration even
   * when sandwiched between multiple solid obstacles or players.
   * 
   * @param {Object} entity - Dynamic entity { x, y, radius, invMass, vx, vy }
   * @param {Array<Object>} colliders - Array of static/dynamic colliders
   * @param {number} [iterations=2] - Number of relaxation passes
   * @param {number} [friction=0.0] - Sliding friction
   */
  function solveMultipleCollisions(entity, colliders, iterations = 2, friction = 0.0) {
    for (let pass = 0; pass < iterations; pass++) {
      for (let i = 0; i < colliders.length; i++) {
        const col = colliders[i];
        if (!col) continue;
        resolveCollision(entity, col, { slide: pass === 0, friction });
      }
    }
  }

  return {
    resolveCircleCircle,
    resolveCircleBox,
    resolveCollision,
    projectVelocitySlide,
    SmoothReconciler,
    solveMultipleCollisions
  };
}));
