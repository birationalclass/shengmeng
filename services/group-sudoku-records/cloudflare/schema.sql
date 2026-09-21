CREATE TABLE IF NOT EXISTS students (
 id TEXT PRIMARY KEY,
 name TEXT NOT NULL,
 initials TEXT NOT NULL CHECK(length(initials)>0 AND initials NOT GLOB '*[^A-Z]*')
);
CREATE TABLE IF NOT EXISTS completions (
 student_id TEXT PRIMARY KEY REFERENCES students(id),
 first_at TEXT NOT NULL,
 updated_at TEXT NOT NULL,
 submission_id TEXT NOT NULL UNIQUE,
 boards TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS requests (
 id TEXT PRIMARY KEY,
 student_id TEXT NOT NULL REFERENCES students(id),
 created_at TEXT NOT NULL,
 boards TEXT NOT NULL
);
-- One atomic insert drives both retry deduplication and completion updates.
CREATE TRIGGER IF NOT EXISTS completion_from_request AFTER INSERT ON requests BEGIN
 INSERT INTO completions(student_id,first_at,updated_at,submission_id,boards)
 VALUES(NEW.student_id,NEW.created_at,NEW.created_at,NEW.id,NEW.boards)
 ON CONFLICT(student_id) DO UPDATE SET
 updated_at=excluded.updated_at,submission_id=excluded.submission_id,boards=excluded.boards;
END;
CREATE TABLE IF NOT EXISTS rate_limits (
 key TEXT PRIMARY KEY,
 minute INTEGER NOT NULL,
 count INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS rate_expiry ON rate_limits(minute);
