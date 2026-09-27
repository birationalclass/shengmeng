import assert from 'node:assert/strict';
import {acceptsStartupQuality as accepts} from './startup-probe.js';
assert(accepts(Array(16).fill(16.7),[7,8,9]));assert(!accepts(Array(16).fill(33),[9]));assert(!accepts(Array(16).fill(16.7),[19]));assert(!accepts([16]));assert(!accepts([...Array(12).fill(16),40,40,40,40]));console.log('PASS startup quality probe rejects slow frames, GPU overload and insufficient samples');
