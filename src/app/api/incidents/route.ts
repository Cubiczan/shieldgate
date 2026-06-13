import { NextResponse } from 'next/server';
import { db } from '@/lib/db';
import { withAuth, type AuthenticatedRequest } from '@/lib/auth-middleware';
import type { UserRole } from '@/lib/authz-types';

// Allowlist of incident statuses a caller may transition an incident to.
// Anything outside this set is rejected (no free-form status injection).
const ALLOWED_STATUSES = new Set(['open', 'investigating', 'resolved', 'closed']);

// Roles permitted to mutate incident status. Mirrors the SpiceDB `resolve`
// permission intent: triage-only / external roles cannot change incident state.
const STATUS_WRITE_ROLES = new Set<UserRole>(['soc_tier2', 'sre', 'ai_agent']);

export const GET = withAuth(async (request: AuthenticatedRequest) => {
  const incidents = await db.incident.findMany({
    orderBy: { createdAt: 'desc' },
  });
  return NextResponse.json(incidents);
});

export const PATCH = withAuth(async (request: AuthenticatedRequest) => {
  try {
    // Authorization: only senior/automation roles may change incident status.
    if (!STATUS_WRITE_ROLES.has(request.authRole)) {
      return NextResponse.json(
        {
          error: 'PERMISSION_DENIED',
          reason: `Role '${request.authRole}' is not authorized to update incident status`,
          policy: 'least_privilege',
        },
        { status: 403 },
      );
    }

    const body = await request.json();
    const { id, status } = body as { id: string; status: string };

    if (!id || !status) {
      return NextResponse.json({ error: 'id and status are required' }, { status: 400 });
    }

    // Status allowlist: reject any value not in the known set.
    if (!ALLOWED_STATUSES.has(status)) {
      return NextResponse.json(
        {
          error: 'INVALID_STATUS',
          reason: `Status '${status}' is not allowed. Allowed: ${[...ALLOWED_STATUSES].join(', ')}`,
        },
        { status: 400 },
      );
    }

    const updated = await db.incident.update({
      where: { id },
      data: { status },
    });

    return NextResponse.json(updated);
  } catch (error) {
    return NextResponse.json({ error: 'Failed to update incident' }, { status: 500 });
  }
});
