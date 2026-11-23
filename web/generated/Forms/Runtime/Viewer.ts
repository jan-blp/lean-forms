// Generated from Lean. Run npm --prefix web run generate.
export type Document = { "pages": Page[] };
export type Page = { "number": number; "width": number; "height": number; "cells": Cell[] };
export type Cell = { "id": number; "x": number; "y": number; "width": number; "height": number; "text": string };
