// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * Deno development server for ECHIDNA UI
 * Serves static files and proxies API requests to Rust backend
 */

import { serve } from "@std/http";
import { serveDir } from "https://deno.land/std@0.211.0/http/file_server.ts";
import { join } from "@std/path";

const PORT = 8080;
const API_BACKEND = Deno.env.get("ECHIDNA_API_URL") || "http://localhost:3000";

console.log(`🦔 ECHIDNA UI Server starting on port ${PORT}`);
console.log(`📡 API Backend: ${API_BACKEND}`);

serve(async (req: Request) => {
  const url = new URL(req.url);

  // API proxy to Rust backend
  if (url.pathname.startsWith("/api/")) {
    try {
      const apiUrl = new URL(url.pathname, API_BACKEND);
      apiUrl.search = url.search;

      const response = await fetch(apiUrl, {
        method: req.method,
        headers: req.headers,
        body: req.body,
      });

      return response;
    } catch (error) {
      console.error("API proxy error:", error);
      return new Response(JSON.stringify({ error: "Backend unavailable" }), {
        status: 502,
        headers: { "Content-Type": "application/json" },
      });
    }
  }

  // Serve static files
  return serveDir(req, {
    fsRoot: ".",
    urlRoot: "",
    showDirListing: false,
    showIndex: true,
    enableCors: true,
  });
}, { port: PORT });
