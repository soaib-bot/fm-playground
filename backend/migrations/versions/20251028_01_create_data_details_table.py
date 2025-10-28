"""create data_details table

Revision ID: 20251028_01
Revises: b5d5f9a0389d
Create Date: 2025-10-28 00:00:00.000000

"""

from alembic import op
import sqlalchemy as sa

# revision identifiers, used by Alembic.
revision = "20251028_01"
down_revision = "b5d5f9a0389d"
branch_labels = None
depends_on = None


def upgrade():
    op.create_table(
        "data_details",
        sa.Column("id", sa.Integer(), primary_key=True),
        sa.Column("data_id", sa.Integer(), nullable=False, unique=True),
        sa.Column("title", sa.String(), nullable=True),
        sa.Column("tags", sa.String(), nullable=True),
        sa.Column("pinned", sa.Boolean(), nullable=False, server_default="0"),
        sa.Column("created_at", sa.DateTime(), server_default=sa.func.now()),
        sa.Column("updated_at", sa.DateTime(), server_default=sa.func.now()),
        sa.ForeignKeyConstraint(["data_id"], ["data.id"]),
    )
    # create an index on title for faster search later (optional)
    op.create_index("ix_data_details_title", "data_details", ["title"])


def downgrade():
    op.drop_index("ix_data_details_title", table_name="data_details")
    op.drop_table("data_details")
