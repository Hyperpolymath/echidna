/**
 * ECHIDNA HTTP Utilities
 * Deno-native HTTP client utilities with retry logic
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 */

export interface RetryOptions {
  maxRetries: number;
  baseDelayMs: number;
  maxDelayMs: number;
}

const DEFAULT_RETRY: RetryOptions = {
  maxRetries: 3,
  baseDelayMs: 1000,
  maxDelayMs: 16000,
};

/** Sleep for specified milliseconds */
export function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/** Calculate exponential backoff delay */
export function backoffDelay(attempt: number, options: RetryOptions): number {
  const delay = options.baseDelayMs * Math.pow(2, attempt);
  return Math.min(delay, options.maxDelayMs);
}

/** Fetch with exponential backoff retry */
export async function fetchWithRetry(
  url: string | URL,
  init?: RequestInit,
  options: RetryOptions = DEFAULT_RETRY
): Promise<Response> {
  let lastError: Error | null = null;

  for (let attempt = 0; attempt <= options.maxRetries; attempt++) {
    try {
      const response = await fetch(url, init);

      // Retry on server errors
      if (response.status >= 500 && attempt < options.maxRetries) {
        await sleep(backoffDelay(attempt, options));
        continue;
      }

      return response;
    } catch (error) {
      lastError = error instanceof Error ? error : new Error(String(error));

      if (attempt < options.maxRetries) {
        console.warn(`[HTTP] Retry ${attempt + 1}/${options.maxRetries} for ${url}: ${lastError.message}`);
        await sleep(backoffDelay(attempt, options));
      }
    }
  }

  throw new Error(`Failed after ${options.maxRetries} retries: ${lastError?.message}`);
}

/** POST form data (for SystemOnTPTP) */
export async function postForm(
  url: string,
  data: Record<string, string>,
  options?: RetryOptions
): Promise<string> {
  const formData = new URLSearchParams(data);

  const response = await fetchWithRetry(url, {
    method: "POST",
    headers: {
      "Content-Type": "application/x-www-form-urlencoded",
    },
    body: formData.toString(),
  }, options);

  if (!response.ok) {
    throw new Error(`HTTP ${response.status}: ${response.statusText}`);
  }

  return response.text();
}

/** POST JSON */
export async function postJSON<T>(
  url: string,
  data: unknown,
  headers: Record<string, string> = {},
  options?: RetryOptions
): Promise<T> {
  const response = await fetchWithRetry(url, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      ...headers,
    },
    body: JSON.stringify(data),
  }, options);

  if (!response.ok) {
    throw new Error(`HTTP ${response.status}: ${response.statusText}`);
  }

  return response.json();
}

/** GET request */
export async function getText(
  url: string,
  options?: RetryOptions
): Promise<string> {
  const response = await fetchWithRetry(url, {}, options);

  if (!response.ok) {
    throw new Error(`HTTP ${response.status}: ${response.statusText}`);
  }

  return response.text();
}
