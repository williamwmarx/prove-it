const zeroPad = (value: number) => String(value).padStart(2, "0");

// The names of the zones that are UTC, as TZ or /etc/localtime names them, after "Etc/".
const UTC_ZONES = new Set([
  "UTC",
  "UCT",
  "Universal",
  "Zulu",
  "GMT",
  "GMT0",
  "GMT+0",
  "GMT-0",
  "Greenwich",
]);

// Whether the process's local time zone is UTC: TZ names it, or without TZ, /etc/localtime links to
// it. TZ may start with a colon, and may name a zone by its file.
const getIsUtcZone = () => {
  if (typeof process === "undefined") return false;
  const isUtcName = (name: string) =>
    UTC_ZONES.has(
      name
        .replace(/^:/, "")
        .replace(/^.*\/zoneinfo\//, "")
        .replace(/^Etc\//, ""),
    );
  const zone = process.env.TZ;
  if (zone !== undefined) return isUtcName(zone);
  const fs = process.getBuiltinModule?.("node:fs");
  if (fs === undefined) return false;
  const link = fs.lstatSync("/etc/localtime", { throwIfNoEntry: false });
  return link?.isSymbolicLink() === true && isUtcName(fs.readlinkSync("/etc/localtime"));
};

const timeZone: { isUtc?: boolean } = {};

// TLC's SimpleDateFormat("yyyy-MM-dd HH:mm:ss") in the local time zone.
// HACK: Bun's first call on a Date for a local time loads the time zone, which took about 4.4 ms of
// a run's startup, so in a process whose zone is UTC the date comes from toISOString, which needs
// no zone.
export const formatTlcDate = (date: Date) => {
  timeZone.isUtc ??= getIsUtcZone();
  return timeZone.isUtc
    ? date.toISOString().slice(0, 19).replace("T", " ")
    : `${date.getFullYear()}-${zeroPad(date.getMonth() + 1)}-${zeroPad(date.getDate())} ${zeroPad(date.getHours())}:${zeroPad(date.getMinutes())}:${zeroPad(date.getSeconds())}`;
};
