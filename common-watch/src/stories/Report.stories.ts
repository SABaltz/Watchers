import type {Meta, StoryObj} from '@storybook/react';

import Report from "../components/Report";

const meta = {
  title: 'Report/Report',
  component: Report,
  tags: ['autodocs'],
} satisfies Meta<typeof Report>;

export default meta;
type Story = StoryObj<typeof Report>;

export const Primary: Story = {};
