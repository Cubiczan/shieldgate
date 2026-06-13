import type {
  SplunkEvent,
  SplunkQueryResult,
  SplunkIndex,
  SplunkAlert,
} from "./splunk-sim";

import { withTimeout } from "./resilience";

const splunkSdk = require("splunk-sdk");

// Per-call deadline for Splunk SDK callbacks, which expose no native timeout.
// On breach the caller is released with a ResilienceError (kind "timeout").
const SPLUNK_TIMEOUT_MS = 8000;

let service: any = null;

function getSplunkService() {
  if (service) return service;

  const host = process.env.SPLUNK_HOST;
  const port = parseInt(process.env.SPLUNK_PORT || "8089", 10);
  const token = process.env.SPLUNK_TOKEN;
  const scheme = process.env.SPLUNK_SCHEME || "https";

  if (!host || !token) {
    throw new Error("SPLUNK_HOST and SPLUNK_TOKEN must be set in .env.local");
  }

  service = new splunkSdk.Service({
    scheme,
    host,
    port,
    sessionKey: token,
    autologin: false,
  });

  return service;
}

export function isSplunkConfigured(): boolean {
  return !!(process.env.SPLUNK_HOST && process.env.SPLUNK_TOKEN);
}

export async function runSplunkQuery(
  spl: string,
  index?: string
): Promise<SplunkQueryResult> {
  const svc = getSplunkService();
  const sid = `sid_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;
  const start = Date.now();

  return withTimeout(new Promise<SplunkQueryResult>((resolve, reject) => {
    const searchQuery = spl.startsWith("search ") ? spl : `search ${spl}`;

    svc.oneshotSearch(
      searchQuery,
      { output_mode: "json", count: 50 },
      (err: any, results: any) => {
        if (err) {
          reject(new Error(`Splunk query failed: ${err.message || err}`));
          return;
        }

        const parsed =
          typeof results === "string" ? JSON.parse(results) : results;
        const rows: SplunkEvent[] = (parsed.results || []).map((row: any) => ({
          _time: row._time || "",
          _sourcetype: row._sourcetype || row.sourcetype || "",
          _index: row._index || row.index || index || "",
          _raw: row._raw || "",
          ...row,
        }));

        resolve({
          sid,
          results: rows,
          eventCount: rows.length,
          runDurationMs: Date.now() - start,
        });
      }
    );
  }), SPLUNK_TIMEOUT_MS, "Splunk oneshotSearch");
}

export async function getSplunkIndexes(): Promise<SplunkIndex[]> {
  const svc = getSplunkService();

  return withTimeout(new Promise<SplunkIndex[]>((resolve, reject) => {
    svc.indexes().fetch((err: any, indexes: any) => {
      if (err) {
        reject(new Error(`Failed to fetch indexes: ${err.message || err}`));
        return;
      }

      const list = indexes.list();
      const result: SplunkIndex[] = list.map((idx: any) => {
        const props = idx.properties();
        return {
          name: idx.name,
          totalEvents: parseInt(props.totalEventCount || "0", 10),
          dataSizeGB: (
            parseInt(props.currentDBSizeMB || "0", 10) / 1024
          ).toFixed(1),
          retentionDays: parseInt(
            props.frozenTimePeriodInSecs || "0",
            10
          ) / 86400,
          status: props.disabled === "1" ? ("offline" as const) : ("online" as const),
        };
      });

      resolve(result);
    });
  }), SPLUNK_TIMEOUT_MS, "Splunk indexes.fetch");
}

export async function getSplunkAlerts(): Promise<SplunkAlert[]> {
  const svc = getSplunkService();

  return withTimeout(new Promise<SplunkAlert[]>((resolve, reject) => {
    svc.savedSearches().fetch((err: any, searches: any) => {
      if (err) {
        reject(new Error(`Failed to fetch alerts: ${err.message || err}`));
        return;
      }

      const list = searches.list();
      const alerts: SplunkAlert[] = list
        .filter((s: any) => {
          const props = s.properties();
          return props.alert_type !== undefined || props.is_scheduled === "1";
        })
        .map((s: any) => {
          const props = s.properties();
          return {
            id: s.name,
            name: props["alert.display_name"] || s.name,
            severity: props["alert.severity"] || "medium",
            condition: props.search || "",
            triggeredAt: props["triggered_alert_count"]
              ? new Date().toISOString()
              : "",
            status: props.disabled === "1" ? "disabled" : "active",
          };
        });

      resolve(alerts);
    });
  }), SPLUNK_TIMEOUT_MS, "Splunk savedSearches.fetch");
}

export async function getSplunkIndexDetail(
  name: string
): Promise<SplunkIndex | null> {
  const svc = getSplunkService();

  return withTimeout(new Promise<SplunkIndex | null>((resolve, reject) => {
    svc.indexes().fetch((err: any, indexes: any) => {
      if (err) {
        reject(err);
        return;
      }

      const idx = indexes.item(name);
      if (!idx) {
        resolve(null);
        return;
      }

      const props = idx.properties();
      resolve({
        name: idx.name,
        totalEvents: parseInt(props.totalEventCount || "0", 10),
        dataSizeGB: (
          parseInt(props.currentDBSizeMB || "0", 10) / 1024
        ).toFixed(1),
        retentionDays:
          parseInt(props.frozenTimePeriodInSecs || "0", 10) / 86400,
        status: props.disabled === "1" ? "offline" : "online",
      });
    });
  }), SPLUNK_TIMEOUT_MS, "Splunk indexes.fetch (detail)");
}

export { redactEvents } from "./splunk-sim";
