import { NextResponse } from 'next/server';
import { checkToolPermission, checkIndexPermission, getRolePermissions, AuthZUnavailableError } from '@/lib/authz';
import { db } from '@/lib/db';
import { withAuth, type AuthenticatedRequest } from '@/lib/auth-middleware';

export const POST = withAuth(async (request: AuthenticatedRequest) => {
  try {
    const body = await request.json();
    const { action, resource, permissionType } = body as {
      action: string;
      resource?: string;
      permissionType: 'tool' | 'index';
    };
    const role = request.authRole;

    let decision;

    if (permissionType === 'tool') {
      const index = resource?.startsWith('index:') ? resource.slice(6) : undefined;
      decision = await checkToolPermission(role, action, index);
    } else {
      const index = resource || '';
      decision = await checkIndexPermission(role, index, (action as 'read' | 'query') || 'read');
    }

    // Log the decision to the audit trail
    await db.auditLog.create({
      data: {
        userId: `${role}_user`,
        userRole: role,
        action,
        resource: resource || '',
        decision: decision.allowed ? 'ALLOW' : 'DENY',
        reason: decision.reason,
      },
    });

    return NextResponse.json({
      allowed: decision.allowed,
      reason: decision.reason,
      policy: decision.policy,
      timestamp: decision.timestamp,
    });
  } catch (error) {
    if (error instanceof AuthZUnavailableError) throw error;
    return NextResponse.json({ error: 'Permission check failed' }, { status: 500 });
  }
});

export const GET = withAuth(async (request: AuthenticatedRequest) => {
  const role = request.authRole;

  const permissions = getRolePermissions(role);
  return NextResponse.json(permissions);
});
