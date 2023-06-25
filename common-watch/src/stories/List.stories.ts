import type {Meta, StoryObj} from '@storybook/react';

import List from "../components/List";

const meta = {
  title: 'Example/List',
  component: List,
  tags: ['autodocs'],
} satisfies Meta<typeof List>;

export default meta;
type Story = StoryObj<typeof List>;

export const Primary: Story = {};
